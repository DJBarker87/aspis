import V5RelationMainDotGenerated
import V5RelationCompactFinalGenerated
import V5RelationCompactNewGenerated

/-!
# Extracted V5 terminal routing

This file records the exact generated entry route for the main four-value dot
and the exact generated final-weight route for the compact additive state.
It does not pretend that Charon translated the compact `Zip`-based dot: that
standard-library trait translation is a separately named tool limitation.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5RelationTerminalKernelProof

namespace MainDot

open V5RelationMainDotGenerated

abbrev RawQM31 := V5RelationMainDotGenerated.aspis_core.field.QM31
abbrev RawWeights :=
  V5RelationMainDotGenerated.aspis_core.sumcheck.WeightAccumulator

/-- The complete extracted entry dispatch for the terminal main-weight dot.
The input wrapper has exactly four values; the production `log_len = 2`
branch enters `dot_loop0`, while every other shape is kept explicit. -/
theorem extracted_main_dot_entry_exact
    (weights : RawWeights) (values : Array RawQM31 4#usize) :
    V5RelationMainDotGenerated.extract_weight_dot weights values = (do
      let slice ← lift (Array.to_slice values)
      if weights.log_len = 2#u32 then
        if Slice.len slice = 4#usize then
          let iter ←
            SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
              Global weights.components
          V5RelationMainDotGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0
            iter slice V5RelationMainDotGenerated.aspis_core.field.QM31.ZERO
        else
          V5RelationMainDotGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop1
            weights.log_len weights.components slice
            V5RelationMainDotGenerated.aspis_core.field.QM31.ZERO 0#usize
      else
        V5RelationMainDotGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop2
          weights.log_len weights.components slice
          V5RelationMainDotGenerated.aspis_core.field.QM31.ZERO 0#usize) := by
  rfl

/-- Exhaustion of the extracted component iterator returns the accumulated
dot unchanged. -/
theorem extracted_main_dot_component_iterator_done
    (values : Slice RawQM31)
    (iter : core.slice.iter.Iter
      V5RelationMainDotGenerated.aspis_core.sumcheck.WeightComponent)
    (iter' : core.slice.iter.Iter
      V5RelationMainDotGenerated.aspis_core.sumcheck.WeightComponent)
    (total : RawQM31)
    (nextRun : core.slice.iter.IteratorSliceIter.next iter = .ok (none, iter')) :
    V5RelationMainDotGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
      values iter total = .ok (done total) := by
  unfold V5RelationMainDotGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
  simp [nextRun]

end MainDot

namespace CompactFinal

open V5RelationCompactFinalGenerated

abbrev RawQM31 := V5RelationCompactFinalGenerated.aspis_core.field.QM31
abbrev RawCompact :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights

/-- After the ten extracted block iterations, production adds `delta_scale`
to final slot three.  The premise isolates only the external standard-array
iterator semantics; the slot and update are fully generated. -/
theorem extracted_compact_final_success_adds_delta_to_slot_three
    (compact : RawCompact)
    (iter : core.array.iter.IntoIter
      V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalBlock 10#usize)
    (partialOutput output : Array RawQM31 4#usize)
    (intoIter :
      Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
          compact.blocks = .ok iter)
    (loopRun :
      V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop
          iter
          (Array.repeat 4#usize
            V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO) =
        .ok partialOutput)
    (success :
      V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
          compact = .ok output) :
    ∃ slot3 withDelta,
      Array.index_usize partialOutput 3#usize = .ok slot3 ∧
      V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
          slot3 compact.delta_scale = .ok withDelta ∧
      Array.update partialOutput 3#usize withDelta = .ok output := by
  unfold
    V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
    V5RelationCompactFinalGenerated.v5_cu_probe.V5_CU_PROBE_RELATION_FINAL_VALUES
    at success
  have slotIndex : Std.Usize.wrapping_sub 4#usize 1#usize = 3#usize := by
    apply UScalar.eq_of_val_eq
    rw [Std.Usize.wrapping_sub_val_eq, UScalar.size_UScalarTyUsize]
    rcases System.Platform.numBits_eq with h | h <;>
      simp [Usize.size, Usize.numBits, h]
  simp only [slotIndex, intoIter, bind_tc_ok, loopRun] at success
  unfold lift at success
  simp only [bind_tc_ok] at success
  generalize hslot : Array.index_usize partialOutput 3#usize = slotResult at success
  cases slotResult with
  | fail error => cases success
  | div => cases success
  | ok slot3 =>
    simp only [bind_tc_ok] at success
    generalize hadd :
        V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
          slot3 compact.delta_scale = addResult at success
    cases addResult with
    | fail error => cases success
    | div => cases success
    | ok withDelta =>
      simp only [bind_tc_ok] at success
      exact ⟨slot3, withDelta, rfl, hadd, success⟩

/-- The fixed production selector table used by the compact constructor. -/
  theorem extracted_compact_selector_table_exact :
    V5RelationCompactNewGenerated.v5_cu_probe.V5_CU_PROBE_B_BLOCK_SELECTORS =
      Array.make 10#usize
        [0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8,
          28#u8, 29#u8, 30#u8] := by
  unfold V5RelationCompactNewGenerated.v5_cu_probe.V5_CU_PROBE_B_BLOCK_SELECTORS
  rfl

/-- Right-shifting those selectors by three routes blocks zero through six to
final slot zero and blocks seven through nine to final slot three. -/
theorem production_compact_selector_slots_exact :
    Std.U8.wrapping_shr 0#u8 3#u32 = 0#u8 ∧
    Std.U8.wrapping_shr 1#u8 3#u32 = 0#u8 ∧
    Std.U8.wrapping_shr 2#u8 3#u32 = 0#u8 ∧
    Std.U8.wrapping_shr 3#u8 3#u32 = 0#u8 ∧
    Std.U8.wrapping_shr 4#u8 3#u32 = 0#u8 ∧
    Std.U8.wrapping_shr 5#u8 3#u32 = 0#u8 ∧
    Std.U8.wrapping_shr 6#u8 3#u32 = 0#u8 ∧
    Std.U8.wrapping_shr 28#u8 3#u32 = 3#u8 ∧
    Std.U8.wrapping_shr 29#u8 3#u32 = 3#u8 ∧
    Std.U8.wrapping_shr 30#u8 3#u32 = 3#u8 := by
  decide

end CompactFinal

#print axioms MainDot.extracted_main_dot_entry_exact
#print axioms CompactFinal.extracted_compact_final_success_adds_delta_to_slot_three
#print axioms CompactFinal.extracted_compact_selector_table_exact
#print axioms CompactFinal.production_compact_selector_slots_exact

end AspisV5RelationTerminalKernelProof
