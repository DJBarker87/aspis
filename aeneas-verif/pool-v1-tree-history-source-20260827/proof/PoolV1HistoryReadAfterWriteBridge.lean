import PoolV1HistoryPersistBridge
import PoolV1HistoryCodecRoundTripBridge

/-!
# Pool V1 literal history read-after-write bridge

This file composes the exact persistence traces with the production digest
codec.  It proves that later ordered root writes (and the final filled-count
write) preserve every selected root slot, for both an existing page and a new
rollover page.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace PoolV1HistoryReadAfterWriteBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1HistoryPersistGenerated
open PoolV1HistoryPersistBridge

abbrev Digest := PoolV1HistoryPersistBridge.Digest

def rootWindow (data : Slice Std.U8) (slot : Nat) : List Std.U8 :=
  (data.val.drop (64 + slot * 32)).take 32

theorem setSlice_window_before
    (data : Slice Std.U8) (replacement : List Std.U8)
    (windowStart windowLength writeStart : Nat)
    (before : windowStart + windowLength ≤ writeStart) :
    ((data.setSlice! writeStart replacement).val.drop windowStart).take
        windowLength =
      (data.val.drop windowStart).take windowLength := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < windowLength
  · simp only [List.getElem?_take, inside, ↓reduceIte, List.getElem?_drop,
      Slice.setSlice!_val]
    apply List.setSlice!_getElem?_prefix
    omega
  · simp [List.getElem?_take, inside]

theorem setSlice_window_exact
    (data : Slice Std.U8) (replacement : List Std.U8) (start : Nat)
    (replacementLength : replacement.length = 32)
    (inside : start + 32 ≤ data.val.length) :
    ((data.setSlice! start replacement).val.drop start).take 32 = replacement := by
  apply List.ext_getElem?
  intro index
  by_cases indexBound : index < 32
  · simp only [List.getElem?_take, indexBound, ↓reduceIte,
      List.getElem?_drop, Slice.setSlice!_val]
    rw [List.setSlice!_getElem?_middle]
    · simp only [Nat.add_sub_cancel_left]
    · constructor
      · omega
      constructor
      · omega
      · omega
  · simp [List.getElem?_take, indexBound, replacementLength]

theorem setSlice_window_after
    (data : Slice Std.U8) (replacement : List Std.U8)
    (windowStart windowLength writeStart : Nat)
    (after : writeStart + replacement.length ≤ windowStart) :
    ((data.setSlice! writeStart replacement).val.drop windowStart).take
        windowLength =
      (data.val.drop windowStart).take windowLength := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < windowLength
  · simp only [List.getElem?_take, inside, ↓reduceIte, List.getElem?_drop,
      Slice.setSlice!_val]
    apply List.setSlice!_getElem?_suffix
    omega
  · simp [List.getElem?_take, inside]

namespace NewPageWriteTrace

theorem preserves_window_before
    {roots : Slice Digest} {position : Std.Usize}
    {data final : Slice Std.U8}
    (trace : NewPageWriteTrace roots position data final)
    (windowStart windowLength : Nat)
    (before : windowStart + windowLength ≤ 64 + position.val * 32) :
    (final.val.drop windowStart).take windowLength =
      (data.val.drop windowStart).take windowLength := by
  induction trace with
  | done => rfl
  | step position nextPosition data final encoded active nextValue
      encodedExact tail inductionHypothesis =>
      calc
        (final.val.drop windowStart).take windowLength =
            ((data.setSlice! (64 + position.val * 32) encoded.val).val.drop
              windowStart).take windowLength :=
          inductionHypothesis (by omega)
        _ = (data.val.drop windowStart).take windowLength :=
          setSlice_window_before data encoded.val windowStart windowLength
            (64 + position.val * 32) before

theorem selected_slot_exact
    {roots : Slice Digest} {position : Std.Usize}
    {data final : Slice Std.U8}
    (trace : NewPageWriteTrace roots position data final)
    (selected : Nat) (positionLe : position.val ≤ selected)
    (selectedBound : selected < roots.val.length)
    (capacityBound : roots.val.length ≤ 256)
    (dataLength : data.val.length = 8256) :
    ∃ encoded : Array Std.U8 32#usize,
      aspis_statement.atomic_statement.encode_digest_canonical
          roots[selected] = .ok encoded ∧
      rootWindow final selected = encoded.val := by
  induction trace with
  | done position data pastEnd => omega
  | step position nextPosition data final encoded active nextValue
      encodedExact tail inductionHypothesis =>
      by_cases current : selected = position.val
      · subst selected
        refine ⟨encoded, encodedExact, ?_⟩
        rw [rootWindow]
        rw [PoolV1HistoryReadAfterWriteBridge.NewPageWriteTrace.preserves_window_before
          tail (64 + position.val * 32) 32 (by omega)]
        apply setSlice_window_exact
        · simpa using encoded.property
        · omega
      · exact inductionHypothesis (by omega) (by
          rw [Slice.setSlice!_val, List.length_setSlice!, dataLength])

end NewPageWriteTrace

namespace ExistingPageWriteTrace

theorem preserves_window_before
    {base : Std.U16} {roots : Slice Digest} {position : Std.Usize}
    {data final : Slice Std.U8}
    (trace : ExistingPageWriteTrace base roots position data final)
    (windowStart windowLength : Nat)
    (before :
      windowStart + windowLength ≤ 64 + (base.val + position.val) * 32) :
    (final.val.drop windowStart).take windowLength =
      (data.val.drop windowStart).take windowLength := by
  induction trace with
  | done => rfl
  | step position nextPosition data final encoded active nextValue
      encodedExact tail inductionHypothesis =>
      calc
        (final.val.drop windowStart).take windowLength =
            ((data.setSlice!
              (64 + (base.val + position.val) * 32) encoded.val).val.drop
                windowStart).take windowLength :=
          inductionHypothesis (by omega)
        _ = (data.val.drop windowStart).take windowLength :=
          setSlice_window_before data encoded.val windowStart windowLength
            (64 + (base.val + position.val) * 32) before

theorem selected_slot_exact
    {base : Std.U16} {roots : Slice Digest} {position : Std.Usize}
    {data final : Slice Std.U8}
    (trace : ExistingPageWriteTrace base roots position data final)
    (selected : Nat) (positionLe : position.val ≤ selected)
    (selectedBound : selected < roots.val.length)
    (capacityBound : base.val + roots.val.length ≤ 256)
    (dataLength : data.val.length = 8256) :
    ∃ encoded : Array Std.U8 32#usize,
      aspis_statement.atomic_statement.encode_digest_canonical
          roots[selected] = .ok encoded ∧
      rootWindow final (base.val + selected) = encoded.val := by
  induction trace with
  | done position data pastEnd => omega
  | step position nextPosition data final encoded active nextValue
      encodedExact tail inductionHypothesis =>
      by_cases current : selected = position.val
      · subst selected
        refine ⟨encoded, encodedExact, ?_⟩
        rw [rootWindow]
        rw [PoolV1HistoryReadAfterWriteBridge.ExistingPageWriteTrace.preserves_window_before
          tail
          (64 + (base.val + position.val) * 32) 32 (by omega)]
        apply setSlice_window_exact
        · simpa using encoded.property
        · omega
      · exact inductionHypothesis (by omega) (by
          rw [Slice.setSlice!_val, List.length_setSlice!, dataLength])

end ExistingPageWriteTrace

theorem NewPageHeaderTrace.length_eq
    {data : Slice Std.U8} {pool : solana_pubkey.Pubkey}
    {page first : Std.U64} {rootCount : Std.U16}
    {headerData : Slice Std.U8}
    (trace : NewPageHeaderTrace data pool page first rootCount headerData) :
    headerData.length = data.length := by
  rcases trace with ⟨zeroed, magicData, versionData, logData, encodingData,
    poolData, pageData, firstData, zeroedExact, magicExact, versionExact,
    logExact, encodingExact, poolExact, pageExact, firstExact, filledExact⟩
  calc
    headerData.length = firstData.length := by
      rw [filledExact, Slice.setSlice!_length]
    _ = pageData.length := by
      rw [firstExact, Slice.setSlice!_length]
    _ = poolData.length := by
      rw [pageExact, Slice.setSlice!_length]
    _ = encodingData.length := by
      rw [poolExact, Slice.setSlice!_length]
    _ = logData.length := by
      rw [encodingExact, Slice.set_length]
    _ = versionData.length := by
      rw [logExact, Slice.set_length]
    _ = magicData.length := by
      rw [versionExact, Slice.set_length]
    _ = zeroed.length := by
      rw [magicExact, Slice.setSlice!_length]
    _ = data.length := by
      rw [zeroedExact]
      simp [zeroedPage]

theorem new_page_success_selected_root_decodes
    (data : Slice Std.U8) (pool : solana_pubkey.Pubkey)
    (page first : Std.U64) (roots : Slice Digest) (final : Slice Std.U8)
    (selected : Nat)
    (dataLength : data.length = 8256)
    (rootsCapacity : roots.val.length ≤ 256)
    (selectedBound : selected < roots.val.length)
    (canonical : ∀ index : Fin 8, roots[selected].val[index.val].val < m31Prime)
    (run : history.write_new_page_unchecked data pool page first roots = .ok final) :
    decodeDigest (rootWindow final selected) = some roots[selected] := by
  obtain ⟨rootCount, headerData, rootCountExact, headerTrace, loopRun, trace⟩ :=
    write_new_page_success_has_exact_persistence data pool page first roots final
      dataLength rootsCapacity run
  obtain ⟨encoded, encodedExact, slotExact⟩ :=
    PoolV1HistoryReadAfterWriteBridge.NewPageWriteTrace.selected_slot_exact
      trace selected (by scalar_tac) selectedBound rootsCapacity (by
      have header := Classical.choice headerTrace
      simpa only [Slice.length] using
        (PoolV1HistoryReadAfterWriteBridge.NewPageHeaderTrace.length_eq header).trans
          dataLength)
  rw [slotExact]
  exact PoolV1HistoryCodecRoundTripBridge.source_encoder_decoder_round_trip
    roots[selected] encoded canonical encodedExact

theorem existing_page_success_selected_root_decodes
    (data : Slice Std.U8) (header : history.RootPageHeaderV1)
    (roots : Slice Digest) (final : Slice Std.U8) (selected : Nat)
    (dataLength : data.length = 8256)
    (selectedBound : selected < roots.val.length)
    (canonical : ∀ index : Fin 8, roots[selected].val[index.val].val < m31Prime)
    (run : history.append_roots_unchecked data header roots = .ok final) :
    decodeDigest (rootWindow final (header.filled.val + selected)) =
      some roots[selected] := by
  obtain ⟨loopData, filled, capacity, loopRun, trace, filledExact, finalExact⟩ :=
    append_roots_success_has_exact_persistence data header roots final
      dataLength run
  obtain ⟨encoded, encodedExact, slotExact⟩ :=
    PoolV1HistoryReadAfterWriteBridge.ExistingPageWriteTrace.selected_slot_exact
      trace selected (by scalar_tac) selectedBound capacity (by
      simpa using dataLength)
  rw [finalExact, rootWindow]
  rw [setSlice_window_after loopData
    (core.num.U16.to_le_bytes filled).val
    (64 + (header.filled.val + selected) * 32) 32 56 (by
      have bytesLength :
          (core.num.U16.to_le_bytes filled).val.length = 2 := by
        simp [core.num.U16.to_le_bytes]
      omega)]
  rw [← rootWindow, slotExact]
  exact PoolV1HistoryCodecRoundTripBridge.source_encoder_decoder_round_trip
    roots[selected] encoded canonical encodedExact

#print axioms setSlice_window_before
#print axioms setSlice_window_exact
#print axioms setSlice_window_after
#print axioms NewPageWriteTrace.preserves_window_before
#print axioms NewPageWriteTrace.selected_slot_exact
#print axioms ExistingPageWriteTrace.preserves_window_before
#print axioms ExistingPageWriteTrace.selected_slot_exact
#print axioms NewPageHeaderTrace.length_eq
#print axioms new_page_success_selected_root_decodes
#print axioms existing_page_success_selected_root_decodes

end PoolV1HistoryReadAfterWriteBridge
