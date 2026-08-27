import PoolV1HistoryPersist.Funs
import Aeneas.Tactic.Step.Step

/-!
# Pool V1 literal root-page persistence bridge

The translated functions are the exact byte-mutating production functions in
`programs/aspis-pool/src/history.rs`.  This bridge records the exact loop
termination and root-slot write afterimage used by both new-page and existing
page persistence.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PoolV1HistoryPersistBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1HistoryPersistGenerated

abbrev Digest := Array aspis_core.field.M31 8#usize
abbrev RootIter :=
  core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Digest)

theorem write_loop_body_done
    (iter : RootIter) (data : Slice Std.U8)
    (nextRun :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Digest) iter =
        .ok (none, iter)) :
    history.write_new_page_unchecked_loop.body iter data =
      .ok (.done data) := by
  unfold history.write_new_page_unchecked_loop.body
  simp [nextRun]

theorem write_loop_body_exact_root_slot
    (iter nextIter : RootIter) (data : Slice Std.U8)
    (slot : Std.Usize) (root : Digest)
    (slotBound : slot.val < 256)
    (dataLength : data.length = 8256)
    (nextRun :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Digest) iter =
        .ok (some (slot, root), nextIter))
    (flow : ControlFlow (RootIter × Slice Std.U8) (Slice Std.U8))
    (run : history.write_new_page_unchecked_loop.body iter data = .ok flow) :
    ∃ encoded : Array Std.U8 32#usize,
      aspis_statement.atomic_statement.encode_digest_canonical root =
        .ok encoded ∧
      flow = .cont
        (nextIter, data.setSlice! (64 + slot.val * 32) encoded.val) := by
  have h32 : (32#usize : Std.Usize).val = 32 := by scalar_tac
  have h64 : (64#usize : Std.Usize).val = 64 := by scalar_tac
  unfold history.write_new_page_unchecked_loop.body at run
  rw [nextRun] at run
  simp only [bind_tc_ok] at run
  cases scaledRun : slot * 32#usize with
  | fail error => simp [scaledRun] at run
  | div => simp [scaledRun] at run
  | ok scaled =>
      have scaledSpec := Usize.mul_spec (x := slot) (y := 32#usize)
        (by scalar_tac)
      rw [scaledRun] at scaledSpec
      simp only [WP.spec_ok] at scaledSpec
      simp only [h32] at scaledSpec
      have scaledBound : scaled.val ≤ 8160 := by omega
      cases startRun : history.PAGE_ROOTS_OFFSET + scaled with
      | fail error => simp [scaledRun, startRun] at run
      | div => simp [scaledRun, startRun] at run
      | ok start =>
          have startSpec := Usize.add_spec
            (x := history.PAGE_ROOTS_OFFSET) (y := scaled) (by
            simp only [history.PAGE_ROOTS_OFFSET]
            scalar_tac)
          rw [startRun] at startSpec
          simp only [WP.spec_ok] at startSpec
          simp only [history.PAGE_ROOTS_OFFSET, h64] at startSpec
          have startBound : start.val ≤ 8224 := by omega
          cases finishRun : start + 32#usize with
          | fail error => simp [scaledRun, startRun, finishRun] at run
          | div => simp [scaledRun, startRun, finishRun] at run
          | ok finish =>
              have usizeRoom : 8256 ≤ Usize.max := by
                grind
              have finishSpec := Usize.add_spec (x := start) (y := 32#usize)
                (by
                  omega)
              rw [finishRun] at finishSpec
              simp only [WP.spec_ok] at finishSpec
              cases indexRun :
                  core.slice.index.SliceIndexRangeUsizeSlice.index_mut
                    { start, «end» := finish } data with
              | fail error => simp [scaledRun, startRun, finishRun, indexRun] at run
              | div => simp [scaledRun, startRun, finishRun, indexRun] at run
              | ok indexed =>
                  rcases indexed with ⟨target, back⟩
                  have startLeFinish : start ≤ finish := by
                    simp only [UScalar.le_equiv]
                    omega
                  have finishLeData : finish ≤ data.length := by
                    rw [dataLength]
                    omega
                  have indexSpec :=
                    core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec
                      { start, «end» := finish } data startLeFinish finishLeData
                  rw [indexRun] at indexSpec
                  simp only [WP.spec_ok] at indexSpec
                  rcases indexSpec with ⟨targetVal, targetLength, backSpec⟩
                  cases encodeRun :
                      aspis_statement.atomic_statement.encode_digest_canonical root with
                  | fail error =>
                      simp [scaledRun, startRun, finishRun, indexRun,
                        encodeRun] at run
                  | div =>
                      simp [scaledRun, startRun, finishRun, indexRun,
                        encodeRun] at run
                  | ok encoded =>
                      cases copyRun :
                          core.slice.Slice.copy_from_slice core.marker.CopyU8
                            target (Array.to_slice encoded) with
                      | fail error =>
                          simp [scaledRun, startRun, finishRun, indexRun,
                            encodeRun, copyRun, lift] at run
                      | div =>
                          simp [scaledRun, startRun, finishRun, indexRun,
                            encodeRun, copyRun, lift] at run
                      | ok copied =>
                          have targetLength32 : target.length = 32 := by
                            omega
                          have copySpec :=
                            core.slice.Slice.copy_from_slice.step_spec
                              core.marker.CopyU8 target (Array.to_slice encoded)
                              (by simpa using targetLength32)
                          rw [copyRun] at copySpec
                          simp only [WP.spec_ok] at copySpec
                          simp [scaledRun, startRun, finishRun, indexRun,
                            encodeRun, copyRun, lift] at run
                          refine ⟨encoded, rfl, ?_⟩
                          rw [← run, backSpec copied, copySpec]
                          have startExact : start.val = 64 + slot.val * 32 := by
                            omega
                          rw [startExact]
                          rfl

theorem append_loop_body_done
    (base : Std.U16) (iter : RootIter) (data : Slice Std.U8)
    (nextRun :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Digest) iter =
        .ok (none, iter)) :
    history.append_roots_unchecked_loop.body base iter data =
      .ok (.done data) := by
  unfold history.append_roots_unchecked_loop.body
  simp [nextRun]

theorem append_loop_body_exact_root_slot
    (base : Std.U16) (iter nextIter : RootIter) (data : Slice Std.U8)
    (offset : Std.Usize) (root : Digest)
    (slotBound : base.val + offset.val < 256)
    (dataLength : data.length = 8256)
    (nextRun :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Digest) iter =
        .ok (some (offset, root), nextIter))
    (flow : ControlFlow (RootIter × Slice Std.U8) (Slice Std.U8))
    (run : history.append_roots_unchecked_loop.body base iter data = .ok flow) :
    ∃ encoded : Array Std.U8 32#usize,
      aspis_statement.atomic_statement.encode_digest_canonical root =
        .ok encoded ∧
      flow = .cont
        (nextIter,
          data.setSlice! (64 + (base.val + offset.val) * 32) encoded.val) := by
  have h32 : (32#usize : Std.Usize).val = 32 := by scalar_tac
  have h64 : (64#usize : Std.Usize).val = 64 := by scalar_tac
  have baseCast :
      (core.convert.num.FromUsizeU16.from base).val = base.val :=
    core.convert.num.FromUsizeU16.from_val_eq base
  unfold history.append_roots_unchecked_loop.body at run
  rw [nextRun] at run
  simp only [bind_tc_ok] at run
  cases slotRun : core.convert.num.FromUsizeU16.from base + offset with
  | fail error => simp [slotRun, lift] at run
  | div => simp [slotRun, lift] at run
  | ok slot =>
      have slotSpec := Usize.add_spec
        (x := core.convert.num.FromUsizeU16.from base) (y := offset) (by
          have usizeRoom : 256 ≤ Usize.max := by grind
          omega)
      rw [slotRun] at slotSpec
      simp only [WP.spec_ok] at slotSpec
      rw [baseCast] at slotSpec
      have slotSmall : slot.val < 256 := by omega
      cases scaledRun : slot * 32#usize with
      | fail error => simp [slotRun, scaledRun, lift] at run
      | div => simp [slotRun, scaledRun, lift] at run
      | ok scaled =>
          have scaledSpec := Usize.mul_spec (x := slot) (y := 32#usize)
            (by
              have usizeRoom : 8256 ≤ Usize.max := by grind
              simp only [h32]
              omega)
          rw [scaledRun] at scaledSpec
          simp only [WP.spec_ok] at scaledSpec
          simp only [h32] at scaledSpec
          cases startRun : history.PAGE_ROOTS_OFFSET + scaled with
          | fail error => simp [slotRun, scaledRun, startRun, lift] at run
          | div => simp [slotRun, scaledRun, startRun, lift] at run
          | ok start =>
              have startSpec := Usize.add_spec
                (x := history.PAGE_ROOTS_OFFSET) (y := scaled) (by
                  have usizeRoom : 8256 ≤ Usize.max := by grind
                  simp only [history.PAGE_ROOTS_OFFSET, h64]
                  omega)
              rw [startRun] at startSpec
              simp only [WP.spec_ok] at startSpec
              simp only [history.PAGE_ROOTS_OFFSET, h64] at startSpec
              cases finishRun : start + 32#usize with
              | fail error =>
                  simp [slotRun, scaledRun, startRun, finishRun, lift] at run
              | div =>
                  simp [slotRun, scaledRun, startRun, finishRun, lift] at run
              | ok finish =>
                  have finishSpec := Usize.add_spec
                    (x := start) (y := 32#usize) (by
                      have usizeRoom : 8256 ≤ Usize.max := by grind
                      omega)
                  rw [finishRun] at finishSpec
                  simp only [WP.spec_ok] at finishSpec
                  cases indexRun :
                      core.slice.index.SliceIndexRangeUsizeSlice.index_mut
                        { start, «end» := finish } data with
                  | fail error =>
                      simp [slotRun, scaledRun, startRun, finishRun, indexRun,
                        lift] at run
                  | div =>
                      simp [slotRun, scaledRun, startRun, finishRun, indexRun,
                        lift] at run
                  | ok indexed =>
                      rcases indexed with ⟨target, back⟩
                      have startLeFinish : start ≤ finish := by
                        simp only [UScalar.le_equiv]
                        omega
                      have finishLeData : finish ≤ data.length := by
                        rw [dataLength]
                        omega
                      have indexSpec :=
                        core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec
                          { start, «end» := finish } data startLeFinish
                          finishLeData
                      rw [indexRun] at indexSpec
                      simp only [WP.spec_ok] at indexSpec
                      rcases indexSpec with
                        ⟨targetVal, targetLength, backSpec⟩
                      cases encodeRun :
                          aspis_statement.atomic_statement.encode_digest_canonical root with
                      | fail error =>
                          simp [slotRun, scaledRun, startRun, finishRun,
                            indexRun, encodeRun, lift] at run
                      | div =>
                          simp [slotRun, scaledRun, startRun, finishRun,
                            indexRun, encodeRun, lift] at run
                      | ok encoded =>
                          cases copyRun :
                              core.slice.Slice.copy_from_slice core.marker.CopyU8
                                target (Array.to_slice encoded) with
                          | fail error =>
                              simp [slotRun, scaledRun, startRun, finishRun,
                                indexRun, encodeRun, copyRun, lift] at run
                          | div =>
                              simp [slotRun, scaledRun, startRun, finishRun,
                                indexRun, encodeRun, copyRun, lift] at run
                          | ok copied =>
                              have targetLength32 : target.length = 32 := by
                                omega
                              have copySpec :=
                                core.slice.Slice.copy_from_slice.step_spec
                                  core.marker.CopyU8 target
                                  (Array.to_slice encoded)
                                  (by simpa using targetLength32)
                              rw [copyRun] at copySpec
                              simp only [WP.spec_ok] at copySpec
                              simp [slotRun, scaledRun, startRun, finishRun,
                                indexRun, encodeRun, copyRun, lift] at run
                              refine ⟨encoded, rfl, ?_⟩
                              rw [← run, backSpec copied, copySpec]
                              have startExact :
                                  start.val =
                                    64 + (base.val + offset.val) * 32 := by
                                omega
                              rw [startExact]
                              rfl

#print axioms write_loop_body_done
#print axioms write_loop_body_exact_root_slot
#print axioms append_loop_body_done
#print axioms append_loop_body_exact_root_slot

end PoolV1HistoryPersistBridge
