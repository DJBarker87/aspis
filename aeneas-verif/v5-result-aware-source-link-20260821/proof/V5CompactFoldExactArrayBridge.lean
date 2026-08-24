import V5CompactFoldExactFieldBridge

namespace AspisV5CompactFoldExactArrayBridge

open Aeneas Aeneas.Std Result
open AspisV5CompactFoldExactCallerBridge
open AspisV5CompactFoldExactUnrolledTypes

theorem prepared_index_to_legacy {count : Std.Usize}
    (values : Array ExactPrepared count) (index : Std.Usize) :
    (do
      let value ← Array.index_usize values index
      ok (exactToLegacyPrepared value)) =
      Array.index_usize (exactPreparedArrayToLegacy values) index := by
  unfold Array.index_usize exactPreparedArrayToLegacy
  simp only [Array.getElem?_Usize_eq]
  rw [List.getElem?_map]
  generalize values.val[index.val]? = selected
  cases selected <;> simp

theorem block_index_to_legacy {count : Std.Usize}
    (values : Array ExactBlock count) (index : Std.Usize) :
    (do
      let value ← Array.index_usize values index
      ok (exactToLegacyBlock value)) =
      Array.index_usize (exactBlockArrayToLegacy values) index := by
  unfold Array.index_usize exactBlockArrayToLegacy
  simp only [Array.getElem?_Usize_eq]
  rw [List.getElem?_map]
  generalize values.val[index.val]? = selected
  cases selected <;> simp

theorem prepared_index_components_eq {count : Std.Usize}
    (values : Array ExactPrepared count) (index : Std.Usize) :
    (do
      let value ← Array.index_usize values index
      ok value.components) =
    (do
      let value ←
        Array.index_usize (exactPreparedArrayToLegacy values) index
      ok value.components) := by
  unfold Array.index_usize exactPreparedArrayToLegacy
  simp only [Array.getElem?_Usize_eq]
  rw [List.getElem?_map]
  generalize values.val[index.val]? = selected
  cases selected <;> simp [exactToLegacyPrepared]

theorem prepared_channel_index_eq {count : Std.Usize}
    (values : Array ExactPrepared count) (index component channel : Std.Usize) :
    (do
      let value ← Array.index_usize values index
      let row ← Array.index_usize value.components component
      Array.index_usize row channel) =
    (do
      let value ←
        Array.index_usize (exactPreparedArrayToLegacy values) index
      let row ← Array.index_usize value.components component
      Array.index_usize row channel) := by
  unfold Array.index_usize exactPreparedArrayToLegacy
  simp only [Array.getElem?_Usize_eq]
  rw [List.getElem?_map]
  generalize values.val[index.val]? = selected
  cases selected <;> simp [exactToLegacyPrepared]

theorem prepared_channel_bind_eq {count : Std.Usize} {Output : Type}
    (values : Array ExactPrepared count) (index component channel : Std.Usize)
    (continuation : Std.U32 → Result Output) :
    (do
      let value ← Array.index_usize values index
      let row ← Array.index_usize value.components component
      let limb ← Array.index_usize row channel
      continuation limb) =
    (do
      let value ←
        Array.index_usize (exactPreparedArrayToLegacy values) index
      let row ← Array.index_usize value.components component
      let limb ← Array.index_usize row channel
      continuation limb) := by
  unfold Array.index_usize exactPreparedArrayToLegacy
  simp only [Array.getElem?_Usize_eq]
  rw [List.getElem?_map]
  generalize values.val[index.val]? = selected
  cases selected <;> simp [exactToLegacyPrepared]

theorem raw_index_to_legacy {count : Std.Usize}
    (values : Array ExactRaw count) (index : Std.Usize) :
    (do
      let value ← Array.index_usize values index
      ok (exactToLegacyRaw value)) =
      Array.index_usize (exactRawArrayToLegacy values) index := by
  unfold Array.index_usize exactRawArrayToLegacy
  simp only [Array.getElem?_Usize_eq]
  rw [List.getElem?_map]
  generalize values.val[index.val]? = selected
  cases selected <;> simp

theorem raw_index_bind_eq {count : Std.Usize} {Output : Type}
    (values : Array ExactRaw count) (index : Std.Usize)
    (continuation : LegacyRaw → Result Output) :
    (do
      let value ← Array.index_usize values index
      continuation (exactToLegacyRaw value)) =
    (do
      let value ← Array.index_usize (exactRawArrayToLegacy values) index
      continuation value) := by
  unfold Array.index_usize exactRawArrayToLegacy
  simp only [Array.getElem?_Usize_eq]
  rw [List.getElem?_map]
  generalize values.val[index.val]? = selected
  cases selected <;> simp

#print axioms prepared_index_components_eq
#print axioms prepared_index_to_legacy
#print axioms block_index_to_legacy
#print axioms prepared_channel_index_eq
#print axioms prepared_channel_bind_eq
#print axioms raw_index_to_legacy
#print axioms raw_index_bind_eq

end AspisV5CompactFoldExactArrayBridge
