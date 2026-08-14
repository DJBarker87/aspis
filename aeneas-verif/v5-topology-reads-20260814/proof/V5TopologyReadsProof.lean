import V5TopologyReadsGenerated.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_core
set_option maxRecDepth 3000

namespace AspisV5TopologyReadsSourceProof

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

#print axioms level_indices_success_exact
#print axioms group_masks_success_exact
#print axioms slice_u32_partial_eq_success_iff
#print axioms matched_suffix_success_exact
#print axioms matched_suffix_binds_exact_depth_and_literal_indices

end AspisV5TopologyReadsSourceProof
