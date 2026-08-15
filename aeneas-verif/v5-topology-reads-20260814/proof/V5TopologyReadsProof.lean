import V5TopologyReadsGenerated.Funs
import AspisFormal.V5TopologyConstruction

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_core
set_option maxRecDepth 3000

namespace AspisV5TopologyReadsSourceProof

open AspisV5TopologyConstruction
open AspisV5MerkleAuthenticationBinding

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
          exact ⟨Nat.le_of_not_gt hlevelValue, start, finish, hstart, hfinish,
            hbounds.1, hbounds.2, hvalue⟩
        · simp at hindices

def ExactGroupMasksOutput
    (topology : merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (masks : Slice Std.U8) : Prop :=
  ∃ start finish : Std.Usize,
    Array.index_usize topology.group_offsets level = .ok start ∧
    Array.index_usize topology.group_offsets
      (Std.Usize.wrapping_add level 1#usize) = .ok finish ∧
    start.val ≤ finish.val ∧
    finish.val ≤ topology.group_masks.val.length ∧
    masks.val = List.slice start.val finish.val topology.group_masks.val

theorem group_masks_success_exact
    (topology : merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (masks : Slice Std.U8)
    (hmasks : merkle.Radix4BinaryCapTopology.impl.group_masks
      topology level = .ok (some masks)) :
    level.val < topology.radix_levels.val ∧
      ExactGroupMasksOutput topology level masks := by
  unfold merkle.Radix4BinaryCapTopology.impl.group_masks at hmasks
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
          have hlevelValue :
              ¬ topology.radix_levels.val ≤ level.val := by
            simpa only [UScalar.le_equiv] using hnotTooHigh
          exact ⟨Nat.lt_of_not_ge hlevelValue, start, finish, hstart, hfinish,
            hbounds.1, hbounds.2, hvalue⟩
        · simp at hmasks

def ExactMatchedSuffixOutput
    (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : merkle.MatchedRadix4BinaryCapSuffix) : Prop :=
  matched = {
    topology := topology
    radix_level := radixLevel
    binary_depth := binaryDepth
    expected_len := Slice.len indices
  } ∧
  radixLevel.val ≤ topology.radix_levels.val ∧
  U32.checked_sub topology.binary_depth
      (Std.U32.wrapping_mul (UScalar.cast .U32 radixLevel) 2#u32) =
    some binaryDepth ∧
  merkle.Radix4BinaryCapTopology.impl.level_indices topology radixLevel =
    .ok (some indices)

theorem slice_u32_partial_eq_success_iff
    (left right : Slice Std.U32) (value : Bool)
    (heq : core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU32
      left right = .ok value) :
    value = true ↔ left = right := by
  have hspec := core.slice.cmp.PartialEqSlice.eq_homo_spec
    core.cmp.PartialEqU32 left right (by
      intro x y
      simp [core.cmp.impls.PartialEqU32.ne])
  rw [heq] at hspec
  simpa only [WP.spec_ok] using hspec

theorem matched_suffix_success_exact
    (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : merkle.MatchedRadix4BinaryCapSuffix)
    (hmatch : merkle.Radix4BinaryCapTopology.matched_suffix
      topology radixLevel binaryDepth indices = .ok (some matched)) :
    ExactMatchedSuffixOutput topology radixLevel binaryDepth indices matched := by
  unfold merkle.Radix4BinaryCapTopology.matched_suffix at hmatch
  simp only [lift] at hmatch
  split at hmatch
  case isFalse hlevel => simp at hmatch
  case isTrue hlevel =>
    let doubled := Std.U32.wrapping_mul (UScalar.cast .U32 radixLevel) 2#u32
    cases hsub : U32.checked_sub topology.binary_depth doubled with
    | none =>
      dsimp [doubled] at hsub
      simp [hsub, core.option.Option.Insts.CoreCmpPartialEqOption.eq] at hmatch
    | some remainder =>
      dsimp [doubled] at hsub
      by_cases hdepth : remainder = binaryDepth
      · subst remainder
        simp [hsub, core.option.Option.Insts.CoreCmpPartialEqOption.eq] at hmatch
        cases hindices :
            merkle.Radix4BinaryCapTopology.impl.level_indices topology radixLevel with
        | fail error => simp [hindices] at hmatch
        | div => simp [hindices] at hmatch
        | ok maybeIndices =>
          cases maybeIndices with
          | none =>
            simp [hindices] at hmatch
          | some actualIndices =>
            cases hslice : core.slice.cmp.PartialEqSlice.eq
                core.cmp.PartialEqU32 actualIndices indices with
            | fail error => simp [hindices, hslice] at hmatch
            | div => simp [hindices, hslice] at hmatch
            | ok equal =>
              have hequal := slice_u32_partial_eq_success_iff
                actualIndices indices equal hslice
              cases equal with
              | false => simp [hindices, hslice] at hmatch
              | true =>
                have hactual : actualIndices = indices := hequal.mp rfl
                subst actualIndices
                simp [hindices, hslice] at hmatch
                subst matched
                exact ⟨rfl, by simpa using hlevel, hsub, hindices⟩
      · simp [hsub, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
          hdepth] at hmatch

theorem matched_suffix_binds_exact_depth_and_literal_indices
    (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : merkle.MatchedRadix4BinaryCapSuffix)
    (hradixLevels : topology.radix_levels.val ≤ 15)
    (hmatch : merkle.Radix4BinaryCapTopology.matched_suffix
      topology radixLevel binaryDepth indices = .ok (some matched)) :
    topology.binary_depth.val = binaryDepth.val + radixLevel.val * 2 ∧
      ExactLevelIndicesOutput topology radixLevel indices := by
  have hexact := matched_suffix_success_exact topology radixLevel
    binaryDepth indices matched hmatch
  have hlevel := hexact.2.1
  have hchecked := hexact.2.2.1
  have hindices := hexact.2.2.2
  have hradixLevel : radixLevel.val ≤ 15 := by omega
  let doubled :=
    Std.U32.wrapping_mul (UScalar.cast .U32 radixLevel) 2#u32
  have hcastBound : radixLevel.val < 2 ^ UScalarTy.U32.numBits := by
    norm_num
    omega
  have hcast : (UScalar.cast .U32 radixLevel).val = radixLevel.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq .U32 radixLevel hcastBound
  have hdoubled : doubled.val = radixLevel.val * 2 := by
    dsimp [doubled]
    rw [Std.U32.wrapping_mul_val_eq, hcast]
    norm_num
    have hproduct : radixLevel.val * 2 < Std.U32.size := by
      norm_num [Std.U32.size, Std.U32.numBits]
      omega
    exact Nat.mod_eq_of_lt hproduct
  have hsubspec := U32.checked_sub_bv_spec topology.binary_depth doubled
  dsimp [doubled] at hsubspec
  rw [hchecked] at hsubspec
  simp only at hsubspec
  have hdoubledExpanded :
      (Std.U32.wrapping_mul
        (UScalar.cast .U32 radixLevel) 2#u32).val =
        radixLevel.val * 2 := by
    simpa only [doubled] using hdoubled
  rw [hdoubledExpanded] at hsubspec
  have hlevelIndices := level_indices_success_exact topology radixLevel
    indices hindices
  constructor
  · omega
  · exact hlevelIndices.2

/-! ## Connection to the exact shared topology plan

`Radix4BinaryCapTopology::new` is the one source function which the pinned
Charon/Aeneas pair cannot translate: its nested early returns are outside the
current structured-loop support.  The following premise names only the fields
and prefix offsets which that constructor must produce.  Subject to that
single constructor-field premise, the source-extracted read methods above are
proved to return exactly the shared mathematical plan for every released
level.  Parser and hash-loop behavior is not part of this premise.
-/

structure ExactConstructedTopologyFields
    (queries : Finset V5Query)
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

theorem extracted_level_indices_follow_shared_plan
    (queries : Finset V5Query)
    (topology : merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (indices : Slice Std.U32)
    (hfields : ExactConstructedTopologyFields queries topology)
    (hlevel : level.val < 9)
    (hindices : merkle.Radix4BinaryCapTopology.impl.level_indices
      topology level = .ok (some indices)) :
    indices.val.map (fun index => index.val) =
      sharedLevelIndices queries level.val := by
  obtain ⟨_, start, finish, hstart, hfinish, _, _ , hvalue⟩ :=
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

theorem extracted_group_masks_follow_shared_plan
    (queries : Finset V5Query)
    (topology : merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (masks : Slice Std.U8)
    (hfields : ExactConstructedTopologyFields queries topology)
    (hlevel : level.val < 8)
    (hmasks : merkle.Radix4BinaryCapTopology.impl.group_masks
      topology level = .ok (some masks)) :
    masks.val.map (fun mask => mask.val) =
      sharedGroupMasks queries level.val := by
  obtain ⟨_, start, finish, hstart, hfinish, _, _ , hvalue⟩ :=
    group_masks_success_exact topology level masks hmasks
  have hstartVal := hfields.groupOffset level start (by omega) hstart
  let nextLevel := Std.Usize.wrapping_add level 1#usize
  have hnextVal : nextLevel.val = level.val + 1 := by
    exact usize_succ_val_below_ten level (by omega)
  have hfinishVal := hfields.groupOffset nextLevel finish (by omega) hfinish
  have hoffset := sharedGroupMaskPrefixOffset_succ queries level.val hlevel
  rw [hvalue, map_slice, hfields.groupMaskValues,
    hstartVal, hfinishVal, hnextVal]
  simp only [List.slice, hoffset, Nat.add_sub_cancel_left]
  exact flattened_group_mask_slice_is_exact queries level.val hlevel

theorem extracted_matched_suffix_follows_shared_plan
    (queries : Finset V5Query)
    (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : merkle.MatchedRadix4BinaryCapSuffix)
    (hfields : ExactConstructedTopologyFields queries topology)
    (hmatch : merkle.Radix4BinaryCapTopology.matched_suffix
      topology radixLevel binaryDepth indices = .ok (some matched)) :
    radixLevel.val ≤ 8 ∧
      binaryDepth.val + radixLevel.val * 2 = 17 ∧
      indices.val.map (fun index => index.val) =
        sharedLevelIndices queries radixLevel.val := by
  have hexact := matched_suffix_success_exact topology radixLevel
    binaryDepth indices matched hmatch
  have hlevel : radixLevel.val ≤ 8 := by
    rw [← hfields.radixLevels]
    exact hexact.2.1
  have hdepthAndIndices :=
    matched_suffix_binds_exact_depth_and_literal_indices topology radixLevel
      binaryDepth indices matched (by rw [hfields.radixLevels]; omega) hmatch
  refine ⟨hlevel, ?_, ?_⟩
  · rw [← hfields.binaryDepth]
    exact hdepthAndIndices.1.symm
  · exact extracted_level_indices_follow_shared_plan queries topology
      radixLevel indices hfields (by omega) hexact.2.2.2

#print axioms level_indices_success_exact
#print axioms group_masks_success_exact
#print axioms slice_u32_partial_eq_success_iff
#print axioms matched_suffix_success_exact
#print axioms matched_suffix_binds_exact_depth_and_literal_indices
#print axioms extracted_level_indices_follow_shared_plan
#print axioms extracted_group_masks_follow_shared_plan
#print axioms extracted_matched_suffix_follows_shared_plan

end AspisV5TopologyReadsSourceProof
