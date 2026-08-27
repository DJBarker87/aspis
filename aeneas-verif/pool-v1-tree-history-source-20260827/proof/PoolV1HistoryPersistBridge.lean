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

def enumerateSliceAt (values : Slice Digest) (position : Std.Usize) :
    RootIter :=
  { iter := { slice := values, i := position.val }, count := position }

theorem enumerate_slice_at_next
    (values : Slice Digest) (position : Std.Usize)
    (active : position.val < values.val.length) :
    ∃ nextPosition : Std.Usize,
      nextPosition.val = position.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Digest)
          (enumerateSliceAt values position) =
        .ok (some (position, values[position.val]),
          enumerateSliceAt values nextPosition) := by
  have activeLen : position.val < values.len.val := by simpa using active
  have inner :
      (core.iter.traits.iterator.IteratorSliceIter Digest).next
          ({ slice := values, i := position.val } : core.slice.iter.Iter Digest) =
        .ok (some values[position.val],
          ({ slice := values, i := position.val + 1 } :
            core.slice.iter.Iter Digest)) := by
    change core.slice.iter.IteratorSliceIter.next
      ({ slice := values, i := position.val } : core.slice.iter.Iter Digest) = _
    unfold core.slice.iter.IteratorSliceIter.next
    rw [dif_pos activeLen]
  unfold enumerateSliceAt
    core.iter.adapters.enumerate.IteratorEnumerate.next
  rw [inner]
  simp only [bind_tc_ok]
  have countAdd := @UScalar.add_equiv .Usize position 1#usize
  split at countAdd
  · rename_i nextPosition countRun
    refine ⟨nextPosition, countAdd.2.1, ?_⟩
    simp only [countRun, bind_tc_ok]
    simp [countAdd.2.1]
    rfl
  · simp [UScalar.inBounds] at countAdd
    have lengthBound := Slice.length_ineq values
    exfalso
    scalar_tac
  · contradiction

theorem enumerate_slice_at_done
    (values : Slice Digest) (position : Std.Usize)
    (done : values.val.length ≤ position.val) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Digest)
        (enumerateSliceAt values position) =
      .ok (none, enumerateSliceAt values position) := by
  have doneLen : ¬ position.val < values.len.val := by simpa using done
  have inner :
      (core.iter.traits.iterator.IteratorSliceIter Digest).next
          ({ slice := values, i := position.val } : core.slice.iter.Iter Digest) =
        .ok (none,
          ({ slice := values, i := position.val } : core.slice.iter.Iter Digest)) := by
    change core.slice.iter.IteratorSliceIter.next
      ({ slice := values, i := position.val } : core.slice.iter.Iter Digest) = _
    unfold core.slice.iter.IteratorSliceIter.next
    rw [dif_neg doneLen]
  unfold enumerateSliceAt
    core.iter.adapters.enumerate.IteratorEnumerate.next
  rw [inner]
  rfl

inductive NewPageWriteTrace (roots : Slice Digest) :
    Std.Usize → Slice Std.U8 → Slice Std.U8 → Prop
  | done (position : Std.Usize) (data : Slice Std.U8)
      (pastEnd : roots.val.length ≤ position.val) :
      NewPageWriteTrace roots position data data
  | step (position nextPosition : Std.Usize)
      (data final : Slice Std.U8) (encoded : Array Std.U8 32#usize)
      (active : position.val < roots.val.length)
      (nextValue : nextPosition.val = position.val + 1)
      (encodedExact :
        aspis_statement.atomic_statement.encode_digest_canonical
            roots[position.val] = .ok encoded)
      (tail : NewPageWriteTrace roots nextPosition
        (data.setSlice! (64 + position.val * 32) encoded.val) final) :
      NewPageWriteTrace roots position data final

inductive ExistingPageWriteTrace (base : Std.U16) (roots : Slice Digest) :
    Std.Usize → Slice Std.U8 → Slice Std.U8 → Prop
  | done (position : Std.Usize) (data : Slice Std.U8)
      (pastEnd : roots.val.length ≤ position.val) :
      ExistingPageWriteTrace base roots position data data
  | step (position nextPosition : Std.Usize)
      (data final : Slice Std.U8) (encoded : Array Std.U8 32#usize)
      (active : position.val < roots.val.length)
      (nextValue : nextPosition.val = position.val + 1)
      (encodedExact :
        aspis_statement.atomic_statement.encode_digest_canonical
            roots[position.val] = .ok encoded)
      (tail : ExistingPageWriteTrace base roots nextPosition
        (data.setSlice!
          (64 + (base.val + position.val) * 32) encoded.val) final) :
      ExistingPageWriteTrace base roots position data final

theorem ExistingPageWriteTrace.length_eq
    {base : Std.U16} {roots : Slice Digest} {position : Std.Usize}
    {data final : Slice Std.U8}
    (trace : ExistingPageWriteTrace base roots position data final) :
    final.length = data.length := by
  induction trace with
  | done => rfl
  | step _ _ data _ _ _ _ _ _ ih =>
      rw [ih]
      exact Slice.setSlice!_length _ _ _

def zeroedPage (data : Slice Std.U8) : Slice Std.U8 :=
  ⟨List.replicate data.length 0#u8, by
    simpa using Slice.length_ineq data⟩

def newPageHeaderImage
    (data : Slice Std.U8) (pool : solana_pubkey.Pubkey)
    (page first : Std.U64) (rootCount : Std.U16) : Slice Std.U8 :=
  let d0 := zeroedPage data
  let d1 := d0.setSlice! 0 [65#u8, 83#u8, 80#u8, 82#u8]
  let d2 := d1.set 4#usize 1#u8
  let d3 := d2.set 5#usize 8#u8
  let d4 := d3.set 6#usize
    aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  let d5 := d4.setSlice! 8 pool.val
  let d6 := d5.setSlice! 40 (core.num.U64.to_le_bytes page).val
  let d7 := d6.setSlice! 48 (core.num.U64.to_le_bytes first).val
  d7.setSlice! 56 (core.num.U16.to_le_bytes rootCount).val

theorem exact_range_copy_back
    {data target copied : Slice Std.U8} {back : Slice Std.U8 → Slice Std.U8}
    (start finish : Std.Usize) (bytes : Slice Std.U8)
    (startLeFinish : start ≤ finish) (finishLeData : finish ≤ data.length)
    (bytesLength : bytes.length = finish.val - start.val)
    (indexRun :
      core.slice.index.SliceIndexRangeUsizeSlice.index_mut
          { start, «end» := finish } data = .ok (target, back))
    (copyRun :
      core.slice.Slice.copy_from_slice core.marker.CopyU8 target bytes =
        .ok copied) :
    back copied = data.setSlice! start.val bytes.val := by
  have indexSpec :=
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec
      { start, «end» := finish } data startLeFinish finishLeData
  rw [indexRun] at indexSpec
  simp only [WP.spec_ok] at indexSpec
  rcases indexSpec with ⟨targetVal, targetLength, backSpec⟩
  have copySpec := core.slice.Slice.copy_from_slice.step_spec
    core.marker.CopyU8 target bytes (by omega)
  rw [copyRun] at copySpec
  simp only [WP.spec_ok] at copySpec
  rw [backSpec copied, copySpec]

theorem exact_range_to_copy_back
    {data target copied : Slice Std.U8} {back : Slice Std.U8 → Slice Std.U8}
    (finish : Std.Usize) (bytes : Slice Std.U8)
    (finishLeData : finish ≤ data.length)
    (bytesLength : bytes.length = finish.val)
    (indexRun :
      core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
          { «end» := finish } data = .ok (target, back))
    (copyRun :
      core.slice.Slice.copy_from_slice core.marker.CopyU8 target bytes =
        .ok copied) :
    back copied = data.setSlice! 0 bytes.val := by
  have indexSpec :=
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec
      { «end» := finish } data finishLeData
  rw [indexRun] at indexSpec
  simp only [WP.spec_ok] at indexSpec
  rcases indexSpec with ⟨targetVal, targetLength, backSpec⟩
  have copySpec := core.slice.Slice.copy_from_slice.step_spec
    core.marker.CopyU8 target bytes (by omega)
  rw [copyRun] at copySpec
  simp only [WP.spec_ok] at copySpec
  apply (Slice.eq_iff _ _).mpr
  rw [backSpec copied, copySpec]
  simp only [Slice.setSlice!_val]

structure NewPageHeaderTrace
    (data : Slice Std.U8) (pool : solana_pubkey.Pubkey)
    (page first : Std.U64) (rootCount : Std.U16)
    (headerData : Slice Std.U8) : Type where
  zeroed : Slice Std.U8
  magicData : Slice Std.U8
  versionData : Slice Std.U8
  logData : Slice Std.U8
  encodingData : Slice Std.U8
  poolData : Slice Std.U8
  pageData : Slice Std.U8
  firstData : Slice Std.U8
  zeroedExact : zeroed = zeroedPage data
  magicExact : magicData = zeroed.setSlice! 0
    [65#u8, 83#u8, 80#u8, 82#u8]
  versionExact : versionData = magicData.set 4#usize 1#u8
  logExact : logData = versionData.set 5#usize 8#u8
  encodingExact : encodingData = logData.set 6#usize
    aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  poolExact : poolData = encodingData.setSlice!
    history.PAGE_POOL_OFFSET.val pool.val
  pageExact : pageData = poolData.setSlice!
    history.PAGE_NUMBER_OFFSET.val (core.num.U64.to_le_bytes page).val
  firstExact : firstData = pageData.setSlice!
    history.PAGE_FIRST_SEQUENCE_OFFSET.val
    (core.num.U64.to_le_bytes first).val
  filledExact : headerData = firstData.setSlice!
    history.PAGE_FILLED_OFFSET.val
    (core.num.U16.to_le_bytes rootCount).val

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

theorem write_loop_success_has_exact_trace
    (roots : Slice Digest) (position : Std.Usize)
    (data final : Slice Std.U8)
    (positionBound : position.val ≤ roots.val.length)
    (capacityBound : roots.val.length ≤ 256)
    (dataLength : data.length = 8256)
    (run :
      history.write_new_page_unchecked_loop
          (enumerateSliceAt roots position) data = .ok final) :
    NewPageWriteTrace roots position data final := by
  unfold history.write_new_page_unchecked_loop at run
  rw [loop.eq_def] at run
  simp only at run
  by_cases active : position.val < roots.val.length
  · obtain ⟨nextPosition, nextValue, nextRun⟩ :=
      enumerate_slice_at_next roots position active
    generalize bodyRun :
      history.write_new_page_unchecked_loop.body
        (enumerateSliceAt roots position) data = bodyResult at run
    cases bodyResult with
    | fail error => simp at run
    | div => simp at run
    | ok flow =>
        have exact := write_loop_body_exact_root_slot
          (enumerateSliceAt roots position)
          (enumerateSliceAt roots nextPosition) data position
          roots[position.val] (by omega) dataLength nextRun flow bodyRun
        rcases exact with ⟨encoded, encodedExact, flowExact⟩
        cases flow with
        | done completed => cases flowExact
        | cont next =>
            rcases next with ⟨nextIter, nextData⟩
            simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at flowExact
            rcases flowExact with ⟨rfl, rfl⟩
            exact NewPageWriteTrace.step position nextPosition data final
              encoded active nextValue encodedExact
              (write_loop_success_has_exact_trace roots nextPosition
                (data.setSlice! (64 + position.val * 32) encoded.val) final
                (by omega) capacityBound
                (by simpa [Slice.setSlice!_length] using dataLength) run)
  · have pastEnd : roots.val.length ≤ position.val := by omega
    have nextRun := enumerate_slice_at_done roots position pastEnd
    rw [write_loop_body_done (enumerateSliceAt roots position) data nextRun] at run
    cases run
    exact NewPageWriteTrace.done position data pastEnd
termination_by roots.val.length - position.val
decreasing_by omega

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

theorem append_loop_success_has_exact_trace
    (base : Std.U16) (roots : Slice Digest) (position : Std.Usize)
    (data final : Slice Std.U8)
    (positionBound : position.val ≤ roots.val.length)
    (capacityBound : base.val + roots.val.length ≤ 256)
    (dataLength : data.length = 8256)
    (run :
      history.append_roots_unchecked_loop
          (enumerateSliceAt roots position) data base = .ok final) :
    ExistingPageWriteTrace base roots position data final := by
  unfold history.append_roots_unchecked_loop at run
  rw [loop.eq_def] at run
  simp only at run
  by_cases active : position.val < roots.val.length
  · obtain ⟨nextPosition, nextValue, nextRun⟩ :=
      enumerate_slice_at_next roots position active
    generalize bodyRun :
      history.append_roots_unchecked_loop.body base
        (enumerateSliceAt roots position) data = bodyResult at run
    cases bodyResult with
    | fail error => simp at run
    | div => simp at run
    | ok flow =>
        have exact := append_loop_body_exact_root_slot base
          (enumerateSliceAt roots position)
          (enumerateSliceAt roots nextPosition) data position
          roots[position.val] (by omega) dataLength nextRun flow bodyRun
        rcases exact with ⟨encoded, encodedExact, flowExact⟩
        cases flow with
        | done completed => cases flowExact
        | cont next =>
            rcases next with ⟨nextIter, nextData⟩
            simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at flowExact
            rcases flowExact with ⟨rfl, rfl⟩
            exact ExistingPageWriteTrace.step position nextPosition data final
              encoded active nextValue encodedExact
              (append_loop_success_has_exact_trace base roots nextPosition
                (data.setSlice!
                  (64 + (base.val + position.val) * 32) encoded.val) final
                (by omega) capacityBound
                (by simpa [Slice.setSlice!_length] using dataLength) run)
  · have pastEnd : roots.val.length ≤ position.val := by omega
    have nextRun := enumerate_slice_at_done roots position pastEnd
    rw [append_loop_body_done base (enumerateSliceAt roots position) data
      nextRun] at run
    cases run
    exact ExistingPageWriteTrace.done position data pastEnd
termination_by roots.val.length - position.val
decreasing_by omega

theorem append_roots_success_has_exact_persistence
    (data : Slice Std.U8) (header : history.RootPageHeaderV1)
    (roots : Slice Digest) (final : Slice Std.U8)
    (dataLength : data.length = 8256)
    (run : history.append_roots_unchecked data header roots = .ok final) :
    ∃ loopData : Slice Std.U8, ∃ filled : Std.U16,
      header.filled.val + roots.val.length ≤ 256 ∧
      history.append_roots_unchecked_loop
          (enumerateSliceAt roots 0#usize) data header.filled = .ok loopData ∧
      ExistingPageWriteTrace header.filled roots 0#usize data loopData ∧
      filled.val = header.filled.val + roots.val.length ∧
      final = loopData.setSlice! 56 (core.num.U16.to_le_bytes filled).val := by
  unfold history.append_roots_unchecked at run
  simp [lift, core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,
    aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY] at run
  cases totalRun : core.convert.num.FromUsizeU16.from header.filled + roots.len with
  | fail error => simp [totalRun] at run
  | div => simp [totalRun] at run
  | ok total =>
      have totalEquiv := @UScalar.add_equiv .Usize
        (core.convert.num.FromUsizeU16.from header.filled) roots.len
      rw [totalRun] at totalEquiv
      have totalSpec := totalEquiv.2.1
      have fromExact := core.convert.num.FromUsizeU16.from_val_eq header.filled
      by_cases withinCapacity : total.val ≤ 256
      · generalize loopRun :
          history.append_roots_unchecked_loop
            { iter := { slice := roots, i := 0 }, count := 0#usize }
            data header.filled = loopResult at run
        cases loopResult with
        | fail error => simp [totalRun, withinCapacity, massert] at run
        | div => simp [totalRun, withinCapacity, massert] at run
        | ok loopData =>
            have capacityExact :
                header.filled.val + roots.val.length ≤ 256 := by
              change header.filled.val + roots.len.val ≤ 256
              omega
            have loopRun' :
                history.append_roots_unchecked_loop
                    (enumerateSliceAt roots 0#usize) data header.filled =
                  .ok loopData := by
              simpa [enumerateSliceAt] using loopRun
            have zeroBound : (0#usize : Std.Usize).val ≤ roots.val.length := by
              scalar_tac
            have loopTrace := append_loop_success_has_exact_trace
              header.filled roots 0#usize data loopData zeroBound capacityExact
              dataLength loopRun'
            have loopDataLength : loopData.length = 8256 := by
              rw [loopTrace.length_eq, dataLength]
            let rootCount16 : Std.U16 := UScalar.cast .U16 roots.len
            have rootCountExact : rootCount16.val = roots.val.length := by
              simp only [rootCount16, UScalar.cast_val_eq,
                UScalarTy.U16_numBits_eq]
              apply Nat.mod_eq_of_lt
              omega
            cases filledRun : header.filled + rootCount16 with
            | fail error =>
                simp [totalRun, withinCapacity, massert, rootCount16,
                  filledRun] at run
            | div =>
                simp [totalRun, withinCapacity, massert, rootCount16,
                  filledRun] at run
            | ok filled =>
                have filledSpec := U16.add_spec
                  (x := header.filled) (y := rootCount16) (by
                    have u16Room : 256 ≤ U16.max := by scalar_tac
                    omega)
                rw [filledRun] at filledSpec
                simp only [WP.spec_ok] at filledSpec
                cases indexRun :
                    core.slice.index.SliceIndexRangeUsizeSlice.index_mut
                      { start := history.PAGE_FILLED_OFFSET, «end» := 58#usize }
                      loopData with
                | fail error =>
                    simp [totalRun, withinCapacity, massert,
                      rootCount16, filledRun, indexRun] at run
                | div =>
                    simp [totalRun, withinCapacity, massert,
                      rootCount16, filledRun, indexRun] at run
                | ok indexed =>
                    rcases indexed with ⟨target, back⟩
                    have h56 : (56#usize : Std.Usize).val = 56 := by scalar_tac
                    have h58 : (58#usize : Std.Usize).val = 58 := by scalar_tac
                    have startLeEnd : history.PAGE_FILLED_OFFSET ≤ 58#usize := by
                      simp only [UScalar.le_equiv, history.PAGE_FILLED_OFFSET,
                        h56, h58]
                      omega
                    have endLeData : (58#usize : Std.Usize) ≤ loopData.length := by
                      simp only [h58]
                      rw [loopDataLength]
                      omega
                    have indexSpec :=
                      core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec
                        { start := history.PAGE_FILLED_OFFSET, «end» := 58#usize }
                        loopData startLeEnd endLeData
                    rw [indexRun] at indexSpec
                    simp only [WP.spec_ok] at indexSpec
                    rcases indexSpec with ⟨targetVal, targetLength, backSpec⟩
                    cases copyRun :
                        core.slice.Slice.copy_from_slice core.marker.CopyU8 target
                          (Array.to_slice (core.num.U16.to_le_bytes filled)) with
                    | fail error =>
                        simp [totalRun, withinCapacity, massert,
                          rootCount16, filledRun, indexRun, copyRun] at run
                    | div =>
                        simp [totalRun, withinCapacity, massert,
                          rootCount16, filledRun, indexRun, copyRun] at run
                    | ok copied =>
                        have targetLengthTwo : target.length = 2 := by
                          simp only [history.PAGE_FILLED_OFFSET, h56, h58] at targetLength
                          omega
                        have copySpec :=
                          core.slice.Slice.copy_from_slice.step_spec
                            core.marker.CopyU8 target
                            (Array.to_slice (core.num.U16.to_le_bytes filled))
                            (by simpa using targetLengthTwo)
                        rw [copyRun] at copySpec
                        simp only [WP.spec_ok] at copySpec
                        simp [totalRun, withinCapacity, massert,
                          rootCount16, filledRun, indexRun, copyRun] at run
                        refine ⟨loopData, filled, capacityExact, loopRun',
                          loopTrace, ?_, ?_⟩
                        · omega
                        · rw [← run, backSpec copied, copySpec]
                          simp only [history.PAGE_FILLED_OFFSET, h56]
                          rfl
      · simp only [totalRun, bind_tc_ok] at run
        simp [massert, withinCapacity] at run

theorem write_new_page_success_has_exact_persistence
    (data : Slice Std.U8) (pool : solana_pubkey.Pubkey)
    (page first : Std.U64) (roots : Slice Digest) (final : Slice Std.U8)
    (dataLength : data.length = 8256)
    (rootsCapacity : roots.val.length ≤ 256)
    (run : history.write_new_page_unchecked data pool page first roots = .ok final) :
    ∃ rootCount : Std.U16, ∃ headerData : Slice Std.U8,
      rootCount.val = roots.val.length ∧
      Nonempty (NewPageHeaderTrace data pool page first rootCount headerData) ∧
      history.write_new_page_unchecked_loop
          (enumerateSliceAt roots 0#usize) headerData = .ok final ∧
      NewPageWriteTrace roots 0#usize headerData final := by
  unfold history.write_new_page_unchecked at run
  simp [lift, core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,
    aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY,
    aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_MAGIC,
    aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_VERSION,
    aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY_LOG2,
    solana_pubkey.Pubkey.Insts.CoreConvertAsRefSliceU8.as_ref,
    rootsCapacity, massert] at run
  have dataLenScalar : data.len = 8256#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, dataLength]
    scalar_tac
  simp only [dataLenScalar, if_pos] at run
  generalize fillRun :
    core.slice.Slice.fill core.clone.CloneU8 data 0#u8 = fillResult at run
  cases fillResult with
  | fail error => simp [fillRun] at run
  | div => simp [fillRun] at run
  | ok zeroed =>
      simp only [bind_tc_ok] at run
      have fillSpec := core.slice.Slice.fill.spec core.clone.CloneU8 data 0#u8
        (by simp [core.clone.CloneU8])
      rw [fillRun] at fillSpec
      simp only [WP.spec_ok] at fillSpec
      have zeroedExact : zeroed = zeroedPage data := by
        apply (Slice.eq_iff _ _).mpr
        exact fillSpec.2
      have zeroedLength : zeroed.length = 8256 := by
        rw [fillSpec.1, dataLength]
      cases magicIndexRun :
          core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
            { «end» := 4#usize } zeroed with
      | fail error => simp [fillRun, magicIndexRun] at run
      | div => simp [fillRun, magicIndexRun] at run
      | ok indexed =>
          rcases indexed with ⟨magicTarget, magicBack⟩
          simp only [magicIndexRun, bind_tc_ok] at run
          let magic := Array.make 4#usize
            [65#u8, 83#u8, 80#u8, 82#u8]
            aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_MAGIC._proof_5
          cases magicCopyRun :
              core.slice.Slice.copy_from_slice core.marker.CopyU8 magicTarget
                (Array.to_slice magic) with
          | fail error =>
              simp [fillRun, magicIndexRun, magic, magicCopyRun] at run
          | div => simp [fillRun, magicIndexRun, magic, magicCopyRun] at run
          | ok magicCopied =>
              simp only [magic] at magicCopyRun
              change (do
                let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8
                  magicTarget
                  (Array.make 4#usize [65#u8, 83#u8, 80#u8, 82#u8]
                    aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_MAGIC._proof_5).to_slice
                _) = .ok final at run
              rw [magicCopyRun] at run
              simp only [bind_tc_ok] at run
              have magicFinish : (4#usize : Std.Usize) ≤ zeroed.length := by
                rw [zeroedLength]
                scalar_tac
              have magicBackExact := exact_range_to_copy_back 4#usize
                (Array.to_slice magic) magicFinish (by scalar_tac)
                magicIndexRun magicCopyRun
              let magicData := magicBack magicCopied
              have magicDataExact :
                  magicData = (zeroedPage data).setSlice! 0
                    [65#u8, 83#u8, 80#u8, 82#u8] := by
                simp only [magicData, magic] at magicBackExact ⊢
                rw [magicBackExact, zeroedExact]
                rfl
              have magicDataLength : magicData.length = 8256 := by
                rw [magicDataExact, Slice.setSlice!_length]
                simp only [zeroedPage, Slice.length, List.length_replicate,
                  dataLength]
              cases versionRun : magicData.update 4#usize 1#u8 with
              | fail error =>
                  simp [fillRun, magicIndexRun, magic, magicCopyRun,
                    magicData, versionRun] at run
              | div =>
                  simp [fillRun, magicIndexRun, magic, magicCopyRun,
                    magicData, versionRun] at run
              | ok versionData =>
                  simp only [magicData] at versionRun
                  simp only [versionRun, bind_tc_ok] at run
                  have versionSpec := Slice.update_spec magicData 4#usize 1#u8
                    (by rw [magicDataLength]; scalar_tac)
                  rw [versionRun] at versionSpec
                  simp only [WP.spec_ok] at versionSpec
                  cases logRun : versionData.update 5#usize 8#u8 with
                  | fail error =>
                      simp [fillRun, magicIndexRun, magic, magicCopyRun,
                        magicData, versionRun, logRun] at run
                  | div =>
                      simp [fillRun, magicIndexRun, magic, magicCopyRun,
                        magicData, versionRun, logRun] at run
                  | ok logData =>
                      simp only [logRun, bind_tc_ok] at run
                      have versionLength : versionData.length = 8256 := by
                        rw [versionSpec, Slice.set_length, magicDataLength]
                      have logSpec := Slice.update_spec versionData 5#usize 8#u8
                        (by rw [versionLength]; scalar_tac)
                      rw [logRun] at logSpec
                      simp only [WP.spec_ok] at logSpec
                      cases encodingRun : logData.update 6#usize
                          aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION with
                      | fail error =>
                          simp [fillRun, magicIndexRun, magic, magicCopyRun,
                            magicData, versionRun, logRun, encodingRun] at run
                      | div =>
                          simp [fillRun, magicIndexRun, magic, magicCopyRun,
                            magicData, versionRun, logRun, encodingRun] at run
                      | ok encodingData =>
                          simp only [encodingRun, bind_tc_ok] at run
                          have logLength : logData.length = 8256 := by
                            rw [logSpec, Slice.set_length, versionLength]
                          have encodingSpec := Slice.update_spec logData 6#usize
                            aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
                            (by rw [logLength]; scalar_tac)
                          rw [encodingRun] at encodingSpec
                          simp only [WP.spec_ok] at encodingSpec
                          have encodingLength : encodingData.length = 8256 := by
                            rw [encodingSpec, Slice.set_length, logLength]
                          cases poolIndexRun :
                              core.slice.index.SliceIndexRangeUsizeSlice.index_mut
                                { start := history.PAGE_POOL_OFFSET,
                                  «end» := history.PAGE_NUMBER_OFFSET }
                                encodingData with
                          | fail error =>
                              simp [fillRun, magicIndexRun, magic, magicCopyRun,
                                magicData, versionRun, logRun, encodingRun,
                                poolIndexRun] at run
                          | div =>
                              simp [fillRun, magicIndexRun, magic, magicCopyRun,
                                magicData, versionRun, logRun, encodingRun,
                                poolIndexRun] at run
                          | ok poolIndexed =>
                              rcases poolIndexed with ⟨poolTarget, poolBack⟩
                              simp only [poolIndexRun, bind_tc_ok] at run
                              cases poolCopyRun :
                                  core.slice.Slice.copy_from_slice
                                    core.marker.CopyU8 poolTarget
                                    (Array.to_slice pool) with
                              | fail error =>
                                  simp [fillRun, magicIndexRun, magic,
                                    magicCopyRun, magicData, versionRun, logRun,
                                    encodingRun, poolIndexRun, poolCopyRun] at run
                              | div =>
                                  simp [fillRun, magicIndexRun, magic,
                                    magicCopyRun, magicData, versionRun, logRun,
                                    encodingRun, poolIndexRun, poolCopyRun] at run
                              | ok poolCopied =>
                                  change (do
                                    let s5 ← core.slice.Slice.copy_from_slice
                                      core.marker.CopyU8 poolTarget
                                      (Array.to_slice pool)
                                    _) = .ok final at run
                                  rw [poolCopyRun] at run
                                  simp only [bind_tc_ok] at run
                                  have poolBackExact := exact_range_copy_back
                                    history.PAGE_POOL_OFFSET
                                    history.PAGE_NUMBER_OFFSET
                                    (Array.to_slice pool) (by
                                      simp only [history.PAGE_POOL_OFFSET,
                                        history.PAGE_NUMBER_OFFSET,
                                        UScalar.le_equiv]
                                      scalar_tac)
                                    (by
                                      rw [encodingLength]
                                      simp only [history.PAGE_NUMBER_OFFSET]
                                      scalar_tac)
                                    (by
                                      simp only [history.PAGE_POOL_OFFSET,
                                        history.PAGE_NUMBER_OFFSET]
                                      scalar_tac)
                                    poolIndexRun poolCopyRun
                                  let poolData := poolBack poolCopied
                                  have poolLength : poolData.length = 8256 := by
                                    simp only [poolData]
                                    rw [poolBackExact, Slice.setSlice!_length,
                                      encodingLength]
                                  cases pageIndexRun :
                                      core.slice.index.SliceIndexRangeUsizeSlice.index_mut
                                        { start := history.PAGE_NUMBER_OFFSET,
                                          «end» := history.PAGE_FIRST_SEQUENCE_OFFSET }
                                        poolData with
                                  | fail error =>
                                      simp [fillRun, magicIndexRun, magic,
                                        magicCopyRun, magicData, versionRun,
                                        logRun, encodingRun, poolIndexRun,
                                        poolCopyRun, poolData, pageIndexRun] at run
                                  | div =>
                                      simp [fillRun, magicIndexRun, magic,
                                        magicCopyRun, magicData, versionRun,
                                        logRun, encodingRun, poolIndexRun,
                                        poolCopyRun, poolData, pageIndexRun] at run
                                  | ok pageIndexed =>
                                      rcases pageIndexed with ⟨pageTarget, pageBack⟩
                                      simp only [poolData] at pageIndexRun
                                      simp only [pageIndexRun, bind_tc_ok] at run
                                      cases pageCopyRun :
                                          core.slice.Slice.copy_from_slice
                                            core.marker.CopyU8 pageTarget
                                            (Array.to_slice
                                              (core.num.U64.to_le_bytes page)) with
                                      | fail error =>
                                          simp [fillRun, magicIndexRun, magic,
                                            magicCopyRun, magicData, versionRun,
                                            logRun, encodingRun, poolIndexRun,
                                            poolCopyRun, poolData, pageIndexRun,
                                            pageCopyRun] at run
                                      | div =>
                                          simp [fillRun, magicIndexRun, magic,
                                            magicCopyRun, magicData, versionRun,
                                            logRun, encodingRun, poolIndexRun,
                                            poolCopyRun, poolData, pageIndexRun,
                                            pageCopyRun] at run
                                      | ok pageCopied =>
                                          change (do
                                            let s8 ← core.slice.Slice.copy_from_slice
                                              core.marker.CopyU8 pageTarget
                                              (Array.to_slice
                                                (core.num.U64.to_le_bytes page))
                                            _) = .ok final at run
                                          rw [pageCopyRun] at run
                                          simp only [bind_tc_ok] at run
                                          have pageBackExact := exact_range_copy_back
                                            history.PAGE_NUMBER_OFFSET
                                            history.PAGE_FIRST_SEQUENCE_OFFSET
                                            (Array.to_slice
                                              (core.num.U64.to_le_bytes page))
                                            (by
                                              simp only [history.PAGE_NUMBER_OFFSET,
                                                history.PAGE_FIRST_SEQUENCE_OFFSET,
                                                UScalar.le_equiv]
                                              scalar_tac)
                                            (by
                                              rw [poolLength]
                                              simp only [history.PAGE_FIRST_SEQUENCE_OFFSET]
                                              scalar_tac)
                                            (by
                                              simp only [history.PAGE_NUMBER_OFFSET,
                                                history.PAGE_FIRST_SEQUENCE_OFFSET]
                                              scalar_tac)
                                            pageIndexRun pageCopyRun
                                          let pageData := pageBack pageCopied
                                          have pageLength : pageData.length = 8256 := by
                                            simp only [pageData]
                                            rw [pageBackExact,
                                              Slice.setSlice!_length, poolLength]
                                          cases firstIndexRun :
                                              core.slice.index.SliceIndexRangeUsizeSlice.index_mut
                                                { start := history.PAGE_FIRST_SEQUENCE_OFFSET,
                                                  «end» := history.PAGE_FILLED_OFFSET }
                                                pageData with
                                          | fail error =>
                                              simp [fillRun, magicIndexRun,
                                                magic, magicCopyRun, magicData,
                                                versionRun, logRun, encodingRun,
                                                poolIndexRun, poolCopyRun,
                                                poolData, pageIndexRun,
                                                pageCopyRun, pageData,
                                                firstIndexRun] at run
                                          | div =>
                                              simp [fillRun, magicIndexRun,
                                                magic, magicCopyRun, magicData,
                                                versionRun, logRun, encodingRun,
                                                poolIndexRun, poolCopyRun,
                                                poolData, pageIndexRun,
                                                pageCopyRun, pageData,
                                                firstIndexRun] at run
                                          | ok firstIndexed =>
                                              rcases firstIndexed with
                                                ⟨firstTarget, firstBack⟩
                                              simp only [pageData] at firstIndexRun
                                              simp only [firstIndexRun,
                                                bind_tc_ok] at run
                                              cases firstCopyRun :
                                                  core.slice.Slice.copy_from_slice
                                                    core.marker.CopyU8 firstTarget
                                                    (Array.to_slice
                                                      (core.num.U64.to_le_bytes first)) with
                                              | fail error =>
                                                  simp [fillRun, magicIndexRun,
                                                    magic, magicCopyRun, magicData,
                                                    versionRun, logRun, encodingRun,
                                                    poolIndexRun, poolCopyRun,
                                                    poolData, pageIndexRun,
                                                    pageCopyRun, pageData,
                                                    firstIndexRun, firstCopyRun] at run
                                              | div =>
                                                  simp [fillRun, magicIndexRun,
                                                    magic, magicCopyRun, magicData,
                                                    versionRun, logRun, encodingRun,
                                                    poolIndexRun, poolCopyRun,
                                                    poolData, pageIndexRun,
                                                    pageCopyRun, pageData,
                                                    firstIndexRun, firstCopyRun] at run
                                              | ok firstCopied =>
                                                  change (do
                                                    let s11 ←
                                                      core.slice.Slice.copy_from_slice
                                                        core.marker.CopyU8 firstTarget
                                                        (Array.to_slice
                                                          (core.num.U64.to_le_bytes first))
                                                    _) = .ok final at run
                                                  rw [firstCopyRun] at run
                                                  simp only [bind_tc_ok] at run
                                                  have firstBackExact :=
                                                    exact_range_copy_back
                                                      history.PAGE_FIRST_SEQUENCE_OFFSET
                                                      history.PAGE_FILLED_OFFSET
                                                      (Array.to_slice
                                                        (core.num.U64.to_le_bytes first))
                                                      (by
                                                        simp only [history.PAGE_FIRST_SEQUENCE_OFFSET,
                                                          history.PAGE_FILLED_OFFSET,
                                                          UScalar.le_equiv]
                                                        scalar_tac)
                                                      (by
                                                        rw [pageLength]
                                                        simp only [history.PAGE_FILLED_OFFSET]
                                                        scalar_tac)
                                                      (by
                                                        simp only [history.PAGE_FIRST_SEQUENCE_OFFSET,
                                                          history.PAGE_FILLED_OFFSET]
                                                        scalar_tac)
                                                      firstIndexRun firstCopyRun
                                                  let firstData := firstBack firstCopied
                                                  have firstLength :
                                                      firstData.length = 8256 := by
                                                    simp only [firstData]
                                                    rw [firstBackExact,
                                                      Slice.setSlice!_length, pageLength]
                                                  let rootCount : Std.U16 :=
                                                    UScalar.cast .U16 roots.len
                                                  have rootCountExact :
                                                      rootCount.val = roots.val.length := by
                                                    simp only [rootCount,
                                                      UScalar.cast_val_eq,
                                                      UScalarTy.U16_numBits_eq]
                                                    apply Nat.mod_eq_of_lt
                                                    change roots.val.length < 2 ^ 16
                                                    omega
                                                  cases filledIndexRun :
                                                      core.slice.index.SliceIndexRangeUsizeSlice.index_mut
                                                        { start := history.PAGE_FILLED_OFFSET,
                                                          «end» := 58#usize }
                                                        firstData with
                                                  | fail error =>
                                                      simp [fillRun, magicIndexRun,
                                                        magic, magicCopyRun,
                                                        magicData, versionRun,
                                                        logRun, encodingRun,
                                                        poolIndexRun, poolCopyRun,
                                                        poolData, pageIndexRun,
                                                        pageCopyRun, pageData,
                                                        firstIndexRun,
                                                        firstCopyRun, firstData,
                                                        rootCount, filledIndexRun] at run
                                                  | div =>
                                                      simp [fillRun, magicIndexRun,
                                                        magic, magicCopyRun,
                                                        magicData, versionRun,
                                                        logRun, encodingRun,
                                                        poolIndexRun, poolCopyRun,
                                                        poolData, pageIndexRun,
                                                        pageCopyRun, pageData,
                                                        firstIndexRun,
                                                        firstCopyRun, firstData,
                                                        rootCount, filledIndexRun] at run
                                                  | ok filledIndexed =>
                                                      rcases filledIndexed with
                                                        ⟨filledTarget, filledBack⟩
                                                      simp only [firstData] at filledIndexRun
                                                      simp only [filledIndexRun,
                                                        bind_tc_ok] at run
                                                      cases filledCopyRun :
                                                          core.slice.Slice.copy_from_slice
                                                            core.marker.CopyU8
                                                            filledTarget
                                                            (Array.to_slice
                                                              (core.num.U16.to_le_bytes rootCount)) with
                                                      | fail error =>
                                                          simp [fillRun,
                                                            magicIndexRun, magic,
                                                            magicCopyRun, magicData,
                                                            versionRun, logRun,
                                                            encodingRun,
                                                            poolIndexRun,
                                                            poolCopyRun, poolData,
                                                            pageIndexRun,
                                                            pageCopyRun, pageData,
                                                            firstIndexRun,
                                                            firstCopyRun,
                                                            firstData, rootCount,
                                                            filledIndexRun,
                                                            filledCopyRun] at run
                                                      | div =>
                                                          simp [fillRun,
                                                            magicIndexRun, magic,
                                                            magicCopyRun, magicData,
                                                            versionRun, logRun,
                                                            encodingRun,
                                                            poolIndexRun,
                                                            poolCopyRun, poolData,
                                                            pageIndexRun,
                                                            pageCopyRun, pageData,
                                                            firstIndexRun,
                                                            firstCopyRun,
                                                            firstData, rootCount,
                                                            filledIndexRun,
                                                            filledCopyRun] at run
                                                      | ok filledCopied =>
                                                          simp only [rootCount] at filledCopyRun
                                                          change (do
                                                            let s14 ←
                                                              core.slice.Slice.copy_from_slice
                                                                core.marker.CopyU8 filledTarget
                                                                (Array.to_slice
                                                                  (core.num.U16.to_le_bytes
                                                                    rootCount))
                                                            _) = .ok final at run
                                                          rw [filledCopyRun] at run
                                                          simp only [bind_tc_ok] at run
                                                          have filledBackExact :=
                                                            exact_range_copy_back
                                                              history.PAGE_FILLED_OFFSET
                                                              58#usize
                                                              (Array.to_slice
                                                                (core.num.U16.to_le_bytes rootCount))
                                                              (by
                                                                simp only [history.PAGE_FILLED_OFFSET,
                                                                  UScalar.le_equiv]
                                                                scalar_tac)
                                                              (by
                                                                rw [firstLength]
                                                                scalar_tac)
                                                              (by
                                                                simp only [history.PAGE_FILLED_OFFSET]
                                                                scalar_tac)
                                                              filledIndexRun
                                                              filledCopyRun
                                                          let headerData :=
                                                            filledBack filledCopied
                                                          have headerLength :
                                                              headerData.length = 8256 := by
                                                            simp only [headerData]
                                                            rw [filledBackExact,
                                                              Slice.setSlice!_length,
                                                              firstLength]
                                                          have headerTrace :
                                                              NewPageHeaderTrace data pool page
                                                                first rootCount headerData := by
                                                            refine ⟨zeroed, magicData,
                                                              versionData, logData,
                                                              encodingData, poolData,
                                                              pageData, firstData,
                                                              zeroedExact, ?_,
                                                              versionSpec, logSpec,
                                                              encodingSpec, ?_, ?_,
                                                              ?_, ?_⟩
                                                            · rw [magicDataExact,
                                                                zeroedExact]
                                                            · exact poolBackExact
                                                            · exact pageBackExact
                                                            · exact firstBackExact
                                                            · exact filledBackExact
                                                          have loopRun :
                                                              history.write_new_page_unchecked_loop
                                                                  (enumerateSliceAt roots 0#usize)
                                                                  headerData = .ok final := by
                                                            simpa [enumerateSliceAt,
                                                              headerData] using run
                                                          have trace :=
                                                            write_loop_success_has_exact_trace
                                                              roots 0#usize
                                                              headerData final
                                                              (by scalar_tac)
                                                              rootsCapacity
                                                              headerLength
                                                              loopRun
                                                          exact ⟨rootCount,
                                                            headerData,
                                                            rootCountExact,
                                                            ⟨headerTrace⟩,
                                                            loopRun, trace⟩

#print axioms write_loop_body_done
#print axioms write_loop_body_exact_root_slot
#print axioms write_loop_success_has_exact_trace
#print axioms append_loop_body_done
#print axioms append_loop_body_exact_root_slot
#print axioms append_loop_success_has_exact_trace
#print axioms append_roots_success_has_exact_persistence
#print axioms write_new_page_success_has_exact_persistence

end PoolV1HistoryPersistBridge
