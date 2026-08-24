import V5CompactFoldExactBlockBridge

namespace AspisV5CompactFoldExactUnrolledStateBridge

open Aeneas Aeneas.Std Result
open AspisV5CompactFoldExactCallerBridge
open AspisV5CompactFoldExactUnrolledTypes
open AspisV5CompactFoldExactFieldBridge
open AspisV5CompactFoldExactArrayBridge
open AspisV5CompactFoldExactBlockBridge

def exactDeltaFactor (folds : Std.U8) (alpha alpha2 : ExactRaw) :
    Result ExactRaw :=
  match folds with
  | 0#uscalar => ok
      V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE
  | 1#uscalar => ok
      V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE
  | 2#uscalar => ok alpha2
  | 3#uscalar => ok alpha
  | _ => fail Error.panic

def legacyDeltaFactor (folds : Std.U8) (alpha alpha2 : LegacyRaw) :
    Result LegacyRaw :=
  match folds with
  | 0#uscalar => ok V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE
  | 1#uscalar => ok V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE
  | 2#uscalar => ok alpha2
  | 3#uscalar => ok alpha
  | _ => fail Error.panic

theorem delta_factor_released_to_legacy
    (folds : Std.U8) (alpha alpha2 : ExactRaw)
    (foldBound : folds.val < 4) :
    mapResult exactToLegacyRaw (exactDeltaFactor folds alpha alpha2) =
      legacyDeltaFactor folds (exactToLegacyRaw alpha)
        (exactToLegacyRaw alpha2) := by
  have foldCases : folds.val = 0 ∨ folds.val = 1 ∨ folds.val = 2 ∨
      folds.val = 3 := by omega
  rcases foldCases with foldValue | foldValue | foldValue | foldValue
  · have foldExact : folds = (0#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 0
      exact foldValue
    subst folds
    simp [mapResult, exactDeltaFactor, legacyDeltaFactor]
  · have foldExact : folds = (1#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 1
      exact foldValue
    subst folds
    simp [mapResult, exactDeltaFactor, legacyDeltaFactor]
  · have foldExact : folds = (2#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 2
      exact foldValue
    subst folds
    simp [mapResult, exactDeltaFactor, legacyDeltaFactor]
  · have foldExact : folds = (3#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 3
      exact foldValue
    subst folds
    simp [mapResult, exactDeltaFactor, legacyDeltaFactor]

def exactFinishState (state : ExactState)
    (blocks : Array ExactBlock 10#usize) (deltaFactor : ExactRaw) :
    Result ExactState := do
  let deltaHalf ←
    V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.half deltaFactor
  let deltaQuarter ←
    V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.half deltaHalf
  let deltaScale ←
    V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.mul
      state.delta_scale deltaQuarter
  let folds ← lift (Std.U8.wrapping_add state.folds 1#u8)
  ok { blocks := blocks, delta_scale := deltaScale, folds := folds }

def legacyFinishState (state : LegacyState)
    (blocks : Array LegacyBlock 10#usize) (deltaFactor : LegacyRaw) :
    Result LegacyState := do
  let deltaHalf ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half deltaFactor
  let deltaQuarter ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half deltaHalf
  let deltaScale ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      state.delta_scale deltaQuarter
  let folds ← lift (Std.U8.wrapping_add state.folds 1#u8)
  ok { blocks := blocks, delta_scale := deltaScale, folds := folds }

theorem finish_state_to_legacy (state : ExactState)
    (blocks : Array ExactBlock 10#usize) (deltaFactor : ExactRaw) :
    mapResult exactToLegacyState
        (exactFinishState state blocks deltaFactor) =
      legacyFinishState (exactToLegacyState state)
        (exactBlockArrayToLegacy blocks) (exactToLegacyRaw deltaFactor) := by
  unfold exactFinishState legacyFinishState
  simp only [exactToLegacyState_delta_scale, exactToLegacyState_folds]
  apply bind_transport exactToLegacyRaw exactToLegacyState
      _ _ _ _ (half_to_legacy deltaFactor)
  intro deltaHalf
  apply bind_transport exactToLegacyRaw exactToLegacyState
      _ _ _ _ (half_to_legacy deltaHalf)
  intro deltaQuarter
  apply bind_transport exactToLegacyRaw exactToLegacyState
      _ _ _ _ (mul_to_legacy state.delta_scale deltaQuarter)
  intro deltaScale
  simp [mapResult, exactToLegacyState]

def exactReleasedFinish (state : ExactState)
    (blocks : Array ExactBlock 10#usize) (alpha alpha2 : ExactRaw) :
    Result ExactState := do
  let deltaFactor ← exactDeltaFactor state.folds alpha alpha2
  exactFinishState state blocks deltaFactor

def legacyReleasedFinish (state : LegacyState)
    (blocks : Array LegacyBlock 10#usize) (alpha alpha2 : LegacyRaw) :
    Result LegacyState := do
  let deltaFactor ← legacyDeltaFactor state.folds alpha alpha2
  legacyFinishState state blocks deltaFactor

theorem released_finish_to_legacy (state : ExactState)
    (blocks : Array ExactBlock 10#usize) (alpha alpha2 : ExactRaw)
    (foldBound : state.folds.val < 4) :
    mapResult exactToLegacyState
        (exactReleasedFinish state blocks alpha alpha2) =
      legacyReleasedFinish (exactToLegacyState state)
        (exactBlockArrayToLegacy blocks) (exactToLegacyRaw alpha)
        (exactToLegacyRaw alpha2) := by
  unfold exactReleasedFinish legacyReleasedFinish
  simp only [exactToLegacyState_folds]
  apply bind_transport exactToLegacyRaw exactToLegacyState
      _ _ _ _ (delta_factor_released_to_legacy state.folds alpha alpha2
        foldBound)
  intro deltaFactor
  exact finish_state_to_legacy state blocks deltaFactor

@[simp] theorem ten_block_array_to_legacy
    (output0 output1 output2 output3 output4 output5 output6 output7 output8
      output9 : ExactBlock) :
    exactBlockArrayToLegacy (Array.make 10#usize
      [output0, output1, output2, output3, output4, output5, output6, output7,
        output8, output9]) =
      Array.make 10#usize
        [exactToLegacyBlock output0, exactToLegacyBlock output1,
          exactToLegacyBlock output2, exactToLegacyBlock output3,
          exactToLegacyBlock output4, exactToLegacyBlock output5,
          exactToLegacyBlock output6, exactToLegacyBlock output7,
          exactToLegacyBlock output8, exactToLegacyBlock output9] := by
  apply Subtype.ext
  simp only [exactBlockArrayToLegacy, Array.make, List.map_cons, List.map_nil]

theorem exact_unrolled_to_legacy (state : ExactState) (alpha : ExactRaw)
    (foldBound : state.folds.val < 4) :
    mapResult exactToLegacyState
        (AspisV5CompactFoldExactSource.unrolledFold state alpha) =
      V5CompactFoldSource.unrolledFold
        (exactToLegacyState state) (exactToLegacyRaw alpha) := by
  unfold AspisV5CompactFoldExactSource.unrolledFold
    V5CompactFoldSource.unrolledFold
  simp only [exactToLegacyState_blocks, exactToLegacyState_delta_scale,
    exactToLegacyState_folds]
  apply bind_transport exactToLegacyRaw exactToLegacyState
      _ _ _ _ (square_to_legacy alpha)
  intro alpha2
  apply bind_transport exactToLegacyRaw exactToLegacyState
      _ _ _ _ (mul_to_legacy alpha2 alpha)
  intro alpha3
  apply bind_transport exactToLegacyPrepared exactToLegacyState
      _ _ _ _ (prepared_new_to_legacy alpha3)
  intro prepared0
  apply bind_transport exactToLegacyPrepared exactToLegacyState
      _ _ _ _ (prepared_new_to_legacy alpha2)
  intro prepared1
  apply bind_transport exactToLegacyPrepared exactToLegacyState
      _ _ _ _ (prepared_new_to_legacy alpha)
  intro prepared2
  let prepared : Array ExactPrepared 3#usize :=
    Array.make 3#usize [prepared0, prepared1, prepared2]
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 0#usize)
  intro block0
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block0 foldBound)
  intro output0
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 1#usize)
  intro block1
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block1 foldBound)
  intro output1
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 2#usize)
  intro block2
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block2 foldBound)
  intro output2
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 3#usize)
  intro block3
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block3 foldBound)
  intro output3
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 4#usize)
  intro block4
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block4 foldBound)
  intro output4
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 5#usize)
  intro block5
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block5 foldBound)
  intro output5
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 6#usize)
  intro block6
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block6 foldBound)
  intro output6
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 7#usize)
  intro block7
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block7 foldBound)
  intro output7
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 8#usize)
  intro block8
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block8 foldBound)
  intro output8
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (block_index_to_legacy state.blocks 9#usize)
  intro block9
  apply bind_transport exactToLegacyBlock exactToLegacyState
      _ _ _ _ (fold_block_released_to_legacy state.folds alpha alpha2 alpha3
        prepared block9 foldBound)
  intro output9
  let outputs : Array ExactBlock 10#usize := Array.make 10#usize
    [output0, output1, output2, output3, output4, output5, output6, output7,
      output8, output9]
  have foldCases : state.folds.val = 0 ∨ state.folds.val = 1 ∨
      state.folds.val = 2 ∨ state.folds.val = 3 := by omega
  rcases foldCases with foldValue | foldValue | foldValue | foldValue
  · have foldExact : state.folds = (0#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change state.folds.val = 0
      exact foldValue
    rw [foldExact]
    simp only [bind_tc_ok]
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (by
          simpa [mapResult] using half_to_legacy
            V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE)
    intro deltaHalf
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (half_to_legacy deltaHalf)
    intro deltaQuarter
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (mul_to_legacy state.delta_scale deltaQuarter)
    intro deltaScale
    simp [mapResult, exactToLegacyState, outputs]
  · have foldExact : state.folds = (1#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change state.folds.val = 1
      exact foldValue
    rw [foldExact]
    simp only [bind_tc_ok]
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (by
          simpa [mapResult] using half_to_legacy
            V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE)
    intro deltaHalf
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (half_to_legacy deltaHalf)
    intro deltaQuarter
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (mul_to_legacy state.delta_scale deltaQuarter)
    intro deltaScale
    simp [mapResult, exactToLegacyState, outputs]
  · have foldExact : state.folds = (2#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change state.folds.val = 2
      exact foldValue
    rw [foldExact]
    simp only [bind_tc_ok]
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (half_to_legacy alpha2)
    intro deltaHalf
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (half_to_legacy deltaHalf)
    intro deltaQuarter
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (mul_to_legacy state.delta_scale deltaQuarter)
    intro deltaScale
    simp [mapResult, exactToLegacyState, outputs]
  · have foldExact : state.folds = (3#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change state.folds.val = 3
      exact foldValue
    rw [foldExact]
    simp only [bind_tc_ok]
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (half_to_legacy alpha)
    intro deltaHalf
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (half_to_legacy deltaHalf)
    intro deltaQuarter
    apply bind_transport exactToLegacyRaw exactToLegacyState
        _ _ _ _ (mul_to_legacy state.delta_scale deltaQuarter)
    intro deltaScale
    simp [mapResult, exactToLegacyState, outputs]

#print axioms delta_factor_released_to_legacy
#print axioms finish_state_to_legacy
#print axioms released_finish_to_legacy
#print axioms ten_block_array_to_legacy
#print axioms exact_unrolled_to_legacy

end AspisV5CompactFoldExactUnrolledStateBridge
