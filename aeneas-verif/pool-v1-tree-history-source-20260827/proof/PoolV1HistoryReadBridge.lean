import PoolV1HistoryRead.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace PoolV1HistoryReadBridge

open PoolV1HistoryRead

abbrev Digest := Array aspis_core.field.M31 8#usize

theorem range_index_success_exact
    (data : Slice Std.U8) (start finish : Std.Usize) (out : Slice Std.U8)
    (success :
      core.slice.index.SliceIndexRangeUsizeSlice.index
          { start, «end» := finish } data = .ok out) :
    out.val = List.slice start.val finish.val data.val := by
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at success
  split at success
  · rename_i bounds
    simp only [Result.ok.injEq] at success
    subst out
    rfl
  · simp at success

theorem read_retained_root_success_has_exact_source_slice
    (data : Slice Std.U8) (header : history.RootPageHeaderV1)
    (sequence : Std.U64) (root : Digest)
    (run : history.read_retained_root data header sequence = .ok (.Ok root)) :
    ∃ location : aspis_statement.pool_v1.root_history.RootHistoryLocationV1,
      ∃ start : Std.Usize, ∃ bytes : Array Std.U8 32#usize,
        aspis_statement.pool_v1.root_history.root_history_location sequence =
            .ok location ∧
        location.page_number = header.page_number ∧
        location.slot.val < header.filled.val ∧
        start.val = 64 + location.slot.val * 32 ∧
        bytes.val = (data.val.drop start.val).take 32 ∧
        decodeDigest bytes.val = some root := by
  unfold history.read_retained_root at run
  generalize locationRun :
    aspis_statement.pool_v1.root_history.root_history_location sequence =
      locationResult at run
  cases locationResult with
  | fail error => simp [locationRun] at run
  | div => simp [locationRun] at run
  | ok location =>
    simp only [bind_tc_ok] at run
    by_cases pageExact : location.page_number = header.page_number
    · simp [pageExact] at run
      by_cases slotInside : location.slot.val < header.filled.val
      · have notOutside : ¬ header.filled.val ≤ location.slot.val := by omega
        simp only [UScalar.le_equiv, notOutside, ↓reduceIte, lift] at run
        cases mulRun :
            core.convert.num.FromUsizeU16.from location.slot * 32#usize with
        | fail error =>
          change (do
            let delta ←
              core.convert.num.FromUsizeU16.from location.slot * 32#usize
            _) = .ok (core.result.Result.Ok root) at run
          rw [mulRun] at run
          simp at run
        | div =>
          change (do
            let delta ←
              core.convert.num.FromUsizeU16.from location.slot * 32#usize
            _) = .ok (core.result.Result.Ok root) at run
          rw [mulRun] at run
          simp at run
        | ok delta =>
          change (do
            let delta' ←
              core.convert.num.FromUsizeU16.from location.slot * 32#usize
            _) = .ok (core.result.Result.Ok root) at run
          rw [mulRun] at run
          simp only [bind_tc_ok] at run
          cases startRun : history.PAGE_ROOTS_OFFSET + delta with
          | fail error =>
            change (do
              let start ← history.PAGE_ROOTS_OFFSET + delta
              _) = .ok (core.result.Result.Ok root) at run
            rw [startRun] at run
            simp at run
          | div =>
            change (do
              let start ← history.PAGE_ROOTS_OFFSET + delta
              _) = .ok (core.result.Result.Ok root) at run
            rw [startRun] at run
            simp at run
          | ok start =>
            change (do
              let start' ← history.PAGE_ROOTS_OFFSET + delta
              _) = .ok (core.result.Result.Ok root) at run
            rw [startRun] at run
            simp only [bind_tc_ok] at run
            cases finishRun : start + 32#usize with
            | fail error =>
              change (do
                let finish ← start + 32#usize
                _) = .ok (core.result.Result.Ok root) at run
              rw [finishRun] at run
              simp at run
            | div =>
              change (do
                let finish ← start + 32#usize
                _) = .ok (core.result.Result.Ok root) at run
              rw [finishRun] at run
              simp at run
            | ok finish =>
              change (do
                let finish' ← start + 32#usize
                _) = .ok (core.result.Result.Ok root) at run
              rw [finishRun] at run
              simp only [bind_tc_ok] at run
              cases sliceRun :
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) data
                    { start, «end» := finish } with
              | fail error =>
                change (do
                  let slice ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) data
                      { start, «end» := finish }
                  _) = .ok (core.result.Result.Ok root) at run
                rw [sliceRun] at run
                simp at run
              | div =>
                change (do
                  let slice ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) data
                      { start, «end» := finish }
                  _) = .ok (core.result.Result.Ok root) at run
                rw [sliceRun] at run
                simp at run
              | ok slice =>
                change (do
                  let slice' ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) data
                      { start, «end» := finish }
                  _) = .ok (core.result.Result.Ok root) at run
                rw [sliceRun] at run
                simp only [bind_tc_ok] at run
                generalize arrayRun :
                  core.array.TryFromSharedArraySlice.try_from 32#usize slice =
                    arrayResult at run
                cases arrayResult with
                | fail error => simp [arrayRun] at run
                | div => simp [arrayRun] at run
                | ok converted =>
                  cases converted with
                  | Err error =>
                    simp [core.result.Result.unwrap] at run
                  | Ok bytes =>
                    simp only [core.result.Result.unwrap, bind_tc_ok] at run
                    generalize decodeRun :
                      aspis_statement.atomic_statement.decode_digest_canonical
                        bytes = decodeResult at run
                    cases decodeResult with
                    | fail error => simp [decodeRun] at run
                    | div => simp [decodeRun] at run
                    | ok decoded =>
                      cases decoded with
                      | Err error =>
                        simp [core.result.Result.map_err,
                          history.read_retained_root.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorProgramError.call_once]
                          at run
                      | Ok actual =>
                        simp [core.result.Result.map_err] at run
                        have actualExact : actual = root := by
                          simpa using run
                        subst actual
                        have castVal :
                            (core.convert.num.FromUsizeU16.from
                              location.slot).val = location.slot.val := by
                          exact core.convert.num.FromUsizeU16.from_val_eq
                            location.slot
                        have deltaSpec := Usize.mul_spec
                          (x := core.convert.num.FromUsizeU16.from location.slot)
                          (y := 32#usize) (by scalar_tac)
                        rw [mulRun] at deltaSpec
                        simp only [WP.spec_ok] at deltaSpec
                        have deltaVal :
                            delta.val = location.slot.val * 32 := by
                          simpa [castVal] using deltaSpec
                        have startSpec := Usize.add_spec
                          (x := history.PAGE_ROOTS_OFFSET) (y := delta) (by
                            simp only [history.PAGE_ROOTS_OFFSET]
                            scalar_tac)
                        rw [startRun] at startSpec
                        simp only [WP.spec_ok] at startSpec
                        have startVal : start.val = 64 + location.slot.val * 32 := by
                          simpa [history.PAGE_ROOTS_OFFSET, deltaVal] using startSpec
                        have finishSpec := Usize.add_spec
                          (x := start) (y := 32#usize) (by
                            have slotBound : location.slot.val ≤ U16.max := by
                              scalar_tac
                            have startBound :
                                start.val ≤ 64 + U16.max * 32 := by
                              omega
                            scalar_tac)
                        rw [finishRun] at finishSpec
                        simp only [WP.spec_ok] at finishSpec
                        have finishVal : finish.val = start.val + 32 := by
                          simpa using finishSpec
                        have sliceExact := range_index_success_exact data start
                          finish slice (by
                            change
                              core.slice.index.SliceIndexRangeUsizeSlice.index
                                { start, «end» := finish } data = .ok slice
                            exact sliceRun)
                        have arrayExact : bytes.val = slice.val := by
                          unfold core.array.TryFromSharedArraySlice.try_from at arrayRun
                          split at arrayRun
                          · simp only [Result.ok.injEq] at arrayRun
                            cases arrayRun
                            rfl
                          · simp at arrayRun
                        have bytesExact :
                            bytes.val = (data.val.drop start.val).take 32 := by
                          rw [arrayExact, sliceExact]
                          simp only [List.slice]
                          rw [finishVal]
                          simp only [Nat.add_sub_cancel_left]
                        have decodeExact : decodeDigest bytes.val = some root := by
                          unfold
                            aspis_statement.atomic_statement.decode_digest_canonical
                            at decodeRun
                          split at decodeRun <;> simp_all
                        exact ⟨location, start, bytes, rfl, pageExact,
                          slotInside, startVal, bytesExact, decodeExact⟩
      · have outside : header.filled.val ≤ location.slot.val := by omega
        simp [UScalar.le_equiv, outside,
          solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
          at run
    · have pageMismatch :
          (location.page_number != header.page_number) = true := by
        have nbeq := Aeneas.Simp.neq_imp_nbeq location.page_number
          header.page_number pageExact
        simpa using nbeq
      simp [pageMismatch,
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
        at run

#print axioms range_index_success_exact
#print axioms read_retained_root_success_has_exact_source_slice

end PoolV1HistoryReadBridge
