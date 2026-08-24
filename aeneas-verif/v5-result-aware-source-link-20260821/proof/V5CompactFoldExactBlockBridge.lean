import V5CompactFoldExactPreparedSum3Bridge

namespace AspisV5CompactFoldExactBlockBridge

open Aeneas Aeneas.Std Result
open AspisV5CompactFoldExactCallerBridge
open AspisV5CompactFoldExactUnrolledTypes
open AspisV5CompactFoldExactFieldBridge
open AspisV5CompactFoldExactArrayBridge
open AspisV5CompactFoldExactPreparedSumBridge
open AspisV5CompactFoldExactPreparedSum3Bridge

def mapResult {A B : Type} (convert : A → B) (source : Result A) : Result B := do
  let value ← source
  ok (convert value)

theorem bind_transport {A B C D : Type}
    (convertInput : A → B) (convertOutput : C → D)
    (source : Result A) (target : Result B)
    (left : A → Result C) (right : B → Result D)
    (sourceEq : mapResult convertInput source = target)
    (continuationEq : ∀ value,
      mapResult convertOutput (left value) = right (convertInput value)) :
    mapResult convertOutput (do
      let value ← source
      left value) = (do
        let value ← target
        right value) := by
  cases source with
  | fail error =>
      simp [mapResult] at sourceEq ⊢
      rw [← sourceEq]
      rfl
  | div =>
      simp [mapResult] at sourceEq ⊢
      rw [← sourceEq]
      rfl
  | ok value =>
      simp only [mapResult, bind_tc_ok] at sourceEq ⊢
      rw [← sourceEq]
      simpa [mapResult] using continuationEq value

theorem fold_block_zero_to_legacy
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock) :
    mapResult exactToLegacyBlock
        (AspisV5CompactFoldExactSource.foldBlock (0#8#uscalar : Std.U8)
          alpha alpha2 alpha3 prepared block) =
      V5CompactFoldSource.foldBlock (0#8#uscalar : Std.U8)
        (exactToLegacyRaw alpha) (exactToLegacyRaw alpha2)
        (exactToLegacyRaw alpha3) (exactPreparedArrayToLegacy prepared)
        (exactToLegacyBlock block) := by
  rw [AspisV5CompactFoldExactSource.foldBlock.eq_1,
    V5CompactFoldSource.foldBlock.eq_1]
  unfold AspisV5RelationCompactFoldKernelProof.foldZeroBlock
  simp only [
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_scale,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_power_lo,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_power_hi,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_selector]
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (mul_to_legacy block.power_hi block.power_lo)
  intro product
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (sum_products3_arrays_to_legacy prepared
        (Array.make 3#usize [block.power_lo, block.power_hi, product]))
  intro sum
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (by
        simpa [mapResult] using add_to_legacy
          V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE sum)
  intro factor
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (square_to_legacy block.power_hi)
  intro powerLo
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (square_to_legacy powerLo)
  intro powerHi
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (half_to_legacy factor)
  intro halfFactor
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (half_to_legacy halfFactor)
  intro quarterFactor
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (mul_to_legacy block.scale quarterFactor)
  intro scale
  simp [mapResult, exactToLegacyBlock]

theorem fold_block_one_to_legacy
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock) :
    mapResult exactToLegacyBlock
        (AspisV5CompactFoldExactSource.foldBlock (1#8#uscalar : Std.U8)
          alpha alpha2 alpha3 prepared block) =
      V5CompactFoldSource.foldBlock (1#8#uscalar : Std.U8)
        (exactToLegacyRaw alpha) (exactToLegacyRaw alpha2)
        (exactToLegacyRaw alpha3) (exactPreparedArrayToLegacy prepared)
        (exactToLegacyBlock block) := by
  rw [AspisV5CompactFoldExactSource.foldBlock.eq_2,
    V5CompactFoldSource.foldBlock.eq_2]
  unfold AspisV5RelationCompactFoldKernelProof.foldOneBlock
  simp only [
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_scale,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_power_lo,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_power_hi,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_selector]
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (mul_to_legacy block.power_hi block.power_lo)
  intro product
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (sum_products3_arrays_to_legacy prepared
        (Array.make 3#usize [block.power_lo, block.power_hi, product]))
  intro lowerWeighted
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (by
        simpa [mapResult] using add_to_legacy
          V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE
          lowerWeighted)
  intro lower
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (half_to_legacy lower)
  intro lowerHalf
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (half_to_legacy lowerHalf)
  intro lowerQuarter
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (square_to_legacy block.power_hi)
  intro highSquare
  apply bind_transport exactToLegacyPrepared exactToLegacyBlock
      _ _ _ _ (prepared_index_to_legacy prepared 0#usize)
  intro prepared0
  apply bind_transport exactToLegacyPrepared exactToLegacyBlock
      _ _ _ _ (prepared_index_to_legacy prepared 1#usize)
  intro prepared1
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (sum_products2_arrays_to_legacy
        (Array.make 2#usize [prepared0, prepared1])
        (Array.make 2#usize [block.power_lo, block.power_hi]))
  intro upperWeighted
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (by
        simpa [mapResult] using add_to_legacy
          V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE
          upperWeighted)
  intro upper
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (mul_to_legacy highSquare upper)
  intro upperProduct
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (half_to_legacy upperProduct)
  intro upperHalf
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (half_to_legacy upperHalf)
  intro upperQuarter
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (mul_to_legacy block.scale lowerQuarter)
  intro scale
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (mul_to_legacy block.scale upperQuarter)
  intro powerLo
  simp [mapResult, exactToLegacyBlock]

theorem fold_block_two_to_legacy
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock) :
    mapResult exactToLegacyBlock
        (AspisV5CompactFoldExactSource.foldBlock (2#8#uscalar : Std.U8)
          alpha alpha2 alpha3 prepared block) =
      V5CompactFoldSource.foldBlock (2#8#uscalar : Std.U8)
        (exactToLegacyRaw alpha) (exactToLegacyRaw alpha2)
        (exactToLegacyRaw alpha3) (exactPreparedArrayToLegacy prepared)
        (exactToLegacyBlock block) := by
  rw [AspisV5CompactFoldExactSource.foldBlock.eq_3,
    V5CompactFoldSource.foldBlock.eq_3]
  simp only [
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_scale,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_power_lo,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_power_hi,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_selector]
  by_cases lowBit : block.selector &&& 1#u8 = 0#u8
  · rw [if_pos lowBit]
    simp only [lift, bind_tc_ok, lowBit, ↓reduceIte]
    unfold AspisV5RelationCompactFoldKernelProof.foldTwoEvenBlock
    apply bind_transport exactToLegacyPrepared exactToLegacyBlock
        _ _ _ _ (prepared_index_to_legacy prepared 0#usize)
    intro prepared0
    apply bind_transport exactToLegacyRaw exactToLegacyBlock
        _ _ _ _ (prepared_mul_to_legacy prepared0 block.power_lo)
    intro weighted
    apply bind_transport exactToLegacyRaw exactToLegacyBlock
        _ _ _ _ (add_to_legacy block.scale weighted)
    intro factor
    apply bind_transport exactToLegacyRaw exactToLegacyBlock
        _ _ _ _ (half_to_legacy factor)
    intro halfFactor
    apply bind_transport exactToLegacyRaw exactToLegacyBlock
        _ _ _ _ (half_to_legacy halfFactor)
    intro quarterFactor
    simp [mapResult, exactToLegacyBlock]
  · rw [if_neg lowBit]
    simp only [lift, bind_tc_ok, lowBit, ↓reduceIte]
    unfold AspisV5RelationCompactFoldKernelProof.foldTwoOddBlock
    apply bind_transport exactToLegacyPrepared exactToLegacyBlock
        _ _ _ _ (prepared_index_to_legacy prepared 1#usize)
    intro prepared1
    apply bind_transport exactToLegacyPrepared exactToLegacyBlock
        _ _ _ _ (prepared_index_to_legacy prepared 2#usize)
    intro prepared2
    apply bind_transport exactToLegacyRaw exactToLegacyBlock
        _ _ _ _ (sum_products2_arrays_to_legacy
          (Array.make 2#usize [prepared1, prepared2])
          (Array.make 2#usize [block.scale, block.power_lo]))
    intro factor
    apply bind_transport exactToLegacyRaw exactToLegacyBlock
        _ _ _ _ (half_to_legacy factor)
    intro halfFactor
    apply bind_transport exactToLegacyRaw exactToLegacyBlock
        _ _ _ _ (half_to_legacy halfFactor)
    intro quarterFactor
    simp [mapResult, exactToLegacyBlock]

private theorem u8_bitand_three_lt_four (value : Std.U8) :
    (value &&& 3#u8).val < 4 := by
  rw [UScalar.val_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

def exactFoldThreeBlock (factor : ExactRaw) (block : ExactBlock) :
    Result ExactBlock := do
  let halfFactor ←
    V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.half factor
  let quarterFactor ←
    V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.half halfFactor
  let scale ←
    V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.mul
      block.scale quarterFactor
  ok { block with scale }

theorem fold_three_factor_to_legacy (factor : ExactRaw) (block : ExactBlock) :
    mapResult exactToLegacyBlock (exactFoldThreeBlock factor block) =
      AspisV5RelationCompactFoldKernelProof.foldThreeBlock
        (exactToLegacyRaw factor) (exactToLegacyBlock block) := by
  unfold exactFoldThreeBlock
    AspisV5RelationCompactFoldKernelProof.foldThreeBlock
  simp only [
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_scale,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_power_lo,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_power_hi,
    AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_selector]
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (half_to_legacy factor)
  intro halfFactor
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (half_to_legacy halfFactor)
  intro quarterFactor
  apply bind_transport exactToLegacyRaw exactToLegacyBlock
      _ _ _ _ (mul_to_legacy block.scale quarterFactor)
  intro scale
  simp [mapResult, exactToLegacyBlock]

private theorem exact_fold_three_zero
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (0#8#uscalar : Std.U8)) :
    AspisV5CompactFoldExactSource.foldBlock (3#8#uscalar : Std.U8)
        alpha alpha2 alpha3 prepared block =
      exactFoldThreeBlock
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE block := by
  rw [AspisV5CompactFoldExactSource.foldBlock.eq_4]
  simp only [lift, bind_tc_ok]
  rw [selected]
  rfl

private theorem exact_fold_three_one
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (1#8#uscalar : Std.U8)) :
    AspisV5CompactFoldExactSource.foldBlock (3#8#uscalar : Std.U8)
        alpha alpha2 alpha3 prepared block =
      exactFoldThreeBlock alpha3 block := by
  rw [AspisV5CompactFoldExactSource.foldBlock.eq_4]
  simp only [lift, bind_tc_ok]
  rw [selected]
  rfl

private theorem exact_fold_three_two
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (2#8#uscalar : Std.U8)) :
    AspisV5CompactFoldExactSource.foldBlock (3#8#uscalar : Std.U8)
        alpha alpha2 alpha3 prepared block =
      exactFoldThreeBlock alpha2 block := by
  rw [AspisV5CompactFoldExactSource.foldBlock.eq_4]
  simp only [lift, bind_tc_ok]
  rw [selected]
  rfl

private theorem exact_fold_three_three
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (3#8#uscalar : Std.U8)) :
    AspisV5CompactFoldExactSource.foldBlock (3#8#uscalar : Std.U8)
        alpha alpha2 alpha3 prepared block =
      exactFoldThreeBlock alpha block := by
  rw [AspisV5CompactFoldExactSource.foldBlock.eq_4]
  simp only [lift, bind_tc_ok]
  rw [selected]
  rfl

private theorem legacy_fold_three_zero
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (0#8#uscalar : Std.U8)) :
    V5CompactFoldSource.foldBlock (3#8#uscalar : Std.U8)
        (exactToLegacyRaw alpha) (exactToLegacyRaw alpha2)
        (exactToLegacyRaw alpha3) (exactPreparedArrayToLegacy prepared)
        (exactToLegacyBlock block) =
      AspisV5RelationCompactFoldKernelProof.foldThreeBlock
        V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE
        (exactToLegacyBlock block) := by
  rw [V5CompactFoldSource.foldBlock.eq_4]
  simp only [AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_selector]
  rw [selected]
  rfl

private theorem legacy_fold_three_one
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (1#8#uscalar : Std.U8)) :
    V5CompactFoldSource.foldBlock (3#8#uscalar : Std.U8)
        (exactToLegacyRaw alpha) (exactToLegacyRaw alpha2)
        (exactToLegacyRaw alpha3) (exactPreparedArrayToLegacy prepared)
        (exactToLegacyBlock block) =
      AspisV5RelationCompactFoldKernelProof.foldThreeBlock
        (exactToLegacyRaw alpha3) (exactToLegacyBlock block) := by
  rw [V5CompactFoldSource.foldBlock.eq_4]
  simp only [AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_selector]
  rw [selected]
  rfl

private theorem legacy_fold_three_two
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (2#8#uscalar : Std.U8)) :
    V5CompactFoldSource.foldBlock (3#8#uscalar : Std.U8)
        (exactToLegacyRaw alpha) (exactToLegacyRaw alpha2)
        (exactToLegacyRaw alpha3) (exactPreparedArrayToLegacy prepared)
        (exactToLegacyBlock block) =
      AspisV5RelationCompactFoldKernelProof.foldThreeBlock
        (exactToLegacyRaw alpha2) (exactToLegacyBlock block) := by
  rw [V5CompactFoldSource.foldBlock.eq_4]
  simp only [AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_selector]
  rw [selected]
  rfl

private theorem legacy_fold_three_three
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (3#8#uscalar : Std.U8)) :
    V5CompactFoldSource.foldBlock (3#8#uscalar : Std.U8)
        (exactToLegacyRaw alpha) (exactToLegacyRaw alpha2)
        (exactToLegacyRaw alpha3) (exactPreparedArrayToLegacy prepared)
        (exactToLegacyBlock block) =
      AspisV5RelationCompactFoldKernelProof.foldThreeBlock
        (exactToLegacyRaw alpha) (exactToLegacyBlock block) := by
  rw [V5CompactFoldSource.foldBlock.eq_4]
  simp only [AspisV5CompactFoldExactUnrolledTypes.exactToLegacyBlock_selector]
  rw [selected]
  rfl

theorem fold_block_three_to_legacy
    (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock) :
    mapResult exactToLegacyBlock
        (AspisV5CompactFoldExactSource.foldBlock (3#8#uscalar : Std.U8)
          alpha alpha2 alpha3 prepared block) =
      V5CompactFoldSource.foldBlock (3#8#uscalar : Std.U8)
        (exactToLegacyRaw alpha) (exactToLegacyRaw alpha2)
        (exactToLegacyRaw alpha3) (exactPreparedArrayToLegacy prepared)
        (exactToLegacyBlock block) := by
  let pair := Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8
  have pairBound : pair.val < 4 := by
    exact u8_bitand_three_lt_four
      (Std.U8.wrapping_shr block.selector 1#u32)
  have pairCases : pair.val = 0 ∨ pair.val = 1 ∨ pair.val = 2 ∨
      pair.val = 3 := by omega
  rcases pairCases with pairValue | pairValue | pairValue | pairValue
  · have pairExact :
        Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 = 0#u8 := by
      apply UScalar.eq_of_val_eq
      simpa [pair] using pairValue
    rw [exact_fold_three_zero alpha alpha2 alpha3 prepared block pairExact,
      legacy_fold_three_zero alpha alpha2 alpha3 prepared block pairExact]
    simpa [mapResult] using fold_three_factor_to_legacy
      V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE block
  · have pairExact :
        Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 = 1#u8 := by
      apply UScalar.eq_of_val_eq
      simpa [pair] using pairValue
    rw [exact_fold_three_one alpha alpha2 alpha3 prepared block pairExact,
      legacy_fold_three_one alpha alpha2 alpha3 prepared block pairExact]
    exact fold_three_factor_to_legacy alpha3 block
  · have pairExact :
        Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 = 2#u8 := by
      apply UScalar.eq_of_val_eq
      simpa [pair] using pairValue
    rw [exact_fold_three_two alpha alpha2 alpha3 prepared block pairExact,
      legacy_fold_three_two alpha alpha2 alpha3 prepared block pairExact]
    exact fold_three_factor_to_legacy alpha2 block
  · have pairExact :
        Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 = 3#u8 := by
      apply UScalar.eq_of_val_eq
      simpa [pair] using pairValue
    rw [exact_fold_three_three alpha alpha2 alpha3 prepared block pairExact,
      legacy_fold_three_three alpha alpha2 alpha3 prepared block pairExact]
    exact fold_three_factor_to_legacy alpha block

theorem fold_block_released_to_legacy
    (folds : Std.U8) (alpha alpha2 alpha3 : ExactRaw)
    (prepared : Array ExactPrepared 3#usize) (block : ExactBlock)
    (foldBound : folds.val < 4) :
    mapResult exactToLegacyBlock
        (AspisV5CompactFoldExactSource.foldBlock folds
          alpha alpha2 alpha3 prepared block) =
      V5CompactFoldSource.foldBlock folds
        (exactToLegacyRaw alpha) (exactToLegacyRaw alpha2)
        (exactToLegacyRaw alpha3) (exactPreparedArrayToLegacy prepared)
        (exactToLegacyBlock block) := by
  have foldCases : folds.val = 0 ∨ folds.val = 1 ∨ folds.val = 2 ∨
      folds.val = 3 := by omega
  rcases foldCases with foldValue | foldValue | foldValue | foldValue
  · have foldExact : folds = (0#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 0
      exact foldValue
    subst folds
    exact fold_block_zero_to_legacy alpha alpha2 alpha3 prepared block
  · have foldExact : folds = (1#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 1
      exact foldValue
    subst folds
    exact fold_block_one_to_legacy alpha alpha2 alpha3 prepared block
  · have foldExact : folds = (2#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 2
      exact foldValue
    subst folds
    exact fold_block_two_to_legacy alpha alpha2 alpha3 prepared block
  · have foldExact : folds = (3#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 3
      exact foldValue
    subst folds
    exact fold_block_three_to_legacy alpha alpha2 alpha3 prepared block
#print axioms fold_block_zero_to_legacy
#print axioms fold_block_one_to_legacy
#print axioms fold_block_two_to_legacy
#print axioms fold_block_three_to_legacy
#print axioms fold_block_released_to_legacy

end AspisV5CompactFoldExactBlockBridge
