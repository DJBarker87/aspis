import V5OpeningParserGenerated.Funs
import AspisFormal.V5MerkleConsumedValueBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000

namespace AspisV5OpeningParserSourceProof

open aspis_core
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge

@[simp] theorem usize_from_u16_val (word : Std.U16) :
    (core.convert.num.FromUsizeU16.from word).val = word.val :=
  core.convert.num.FromUsizeU16.from_val_eq word

theorem usize_checked_add_eq_some
    (left right : Std.Usize)
    (hbound : left.val + right.val ≤ Std.Usize.max) :
    ∃ sum : Std.Usize,
      Std.Usize.checked_add left right = some sum ∧
        sum.val = left.val + right.val := by
  have hpow : left.val + right.val < 2 ^ UScalarTy.Usize.numBits := by
    scalar_tac
  have hsystem : left.val + right.val < 2 ^ System.Platform.numBits := by
    simpa using hpow
  let sum : Std.Usize := Std.Usize.ofNatCore (left.val + right.val) hpow
  refine ⟨sum, ?_, by simp [sum]⟩
  unfold Std.Usize.checked_add core.num.checked_add_UScalar
  change Option.ofResult (UScalar.add left right) = some sum
  simp [Option.ofResult, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    Result.ofOption, sum, hsystem]
  apply UScalar.eq_of_val_eq
  simp

theorem usize_checked_mul_eq_some
    (left right : Std.Usize)
    (hbound : left.val * right.val ≤ Std.Usize.max) :
    ∃ product : Std.Usize,
      Std.Usize.checked_mul left right = some product ∧
        product.val = left.val * right.val := by
  have hpow : left.val * right.val < 2 ^ UScalarTy.Usize.numBits := by
    scalar_tac
  have hsystem : left.val * right.val < 2 ^ System.Platform.numBits := by
    simpa using hpow
  let product : Std.Usize := Std.Usize.ofNatCore (left.val * right.val) hpow
  refine ⟨product, ?_, by simp [product]⟩
  unfold Std.Usize.checked_mul core.num.checked_mul_UScalar
  simp [Option.ofResult, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    Result.ofOption, product, hsystem]
  apply UScalar.eq_of_val_eq
  simp

theorem cursor_take_success_exact
    (cursor : state_only_private_openings.Cursor) (len : Std.Usize)
    (hbound : cursor.position.val + len.val ≤ Std.Usize.max)
    (hend : cursor.position.val + len.val ≤ cursor.bytes.val.length) :
    ∃ taken next,
      state_only_private_openings.Cursor.take cursor len =
        .ok (.Ok taken, next) ∧
      taken.val = List.slice cursor.position.val
        (cursor.position.val + len.val) cursor.bytes.val ∧
      next.bytes = cursor.bytes ∧
      next.position.val = cursor.position.val + len.val := by
  obtain ⟨sum, hchecked, hsum⟩ :=
    usize_checked_add_eq_some cursor.position len hbound
  have hnotend : ¬ cursor.bytes.val.length <
      cursor.position.val + len.val := Nat.not_lt.mpr hend
  unfold state_only_private_openings.Cursor.take
  rw [hchecked]
  simp [lift, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    hsum, hend, hnotend]

theorem cursor_take_success_inversion
    (cursor : state_only_private_openings.Cursor) (len : Std.Usize)
    (taken : Slice Std.U8) (next : state_only_private_openings.Cursor)
    (htake : state_only_private_openings.Cursor.take cursor len =
      .ok (.Ok taken, next)) :
    taken.val = List.slice cursor.position.val
        (cursor.position.val + len.val) cursor.bytes.val ∧
      next.bytes = cursor.bytes ∧
      next.position.val = cursor.position.val + len.val ∧
      cursor.position.val + len.val ≤ Std.Usize.max ∧
      cursor.position.val + len.val ≤ cursor.bytes.val.length := by
  unfold state_only_private_openings.Cursor.take at htake
  cases hchecked : Std.Usize.checked_add cursor.position len with
  | none =>
      simp [hchecked, lift, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at htake
  | some sum =>
      have hadd := Std.Usize.checked_add_bv_spec cursor.position len
      simp [hchecked] at hadd
      have hbound : cursor.position.val + len.val ≤ Std.Usize.max := hadd.1
      have hsum : sum.val = cursor.position.val + len.val := hadd.2.1
      by_cases hend : sum.val > cursor.bytes.val.length
      · simp [hchecked, lift, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch, hend] at htake
      · simp [hchecked, lift, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.slice.index.Slice.index,
          core.slice.index.SliceIndexRangeUsizeSlice.index,
          hend, show cursor.position.val ≤ sum.val by omega,
          show sum.val ≤ cursor.bytes.val.length by omega] at htake
        rcases htake with ⟨rfl, rfl⟩
        have hend' : cursor.position.val + len.val ≤
            cursor.bytes.val.length := by omega
        simp [hsum, hbound, hend']

theorem cursor_take_success_length_exact
    (cursor : state_only_private_openings.Cursor) (len : Std.Usize)
    (taken : Slice Std.U8) (next : state_only_private_openings.Cursor)
    (htake : state_only_private_openings.Cursor.take cursor len =
      .ok (.Ok taken, next)) :
    taken.val.length = len.val := by
  have hinv := cursor_take_success_inversion cursor len taken next htake
  rw [hinv.1, List.slice_length]
  have hend := hinv.2.2.2.2
  omega

theorem cursor_u16_success_position_exact
    (cursor : state_only_private_openings.Cursor) (value : Std.U16)
    (next : state_only_private_openings.Cursor)
    (hu16 : state_only_private_openings.Cursor.u16 cursor =
      .ok (.Ok value, next)) :
    next.bytes = cursor.bytes ∧
      next.position.val = cursor.position.val + 2 ∧
      cursor.position.val + 2 ≤ cursor.bytes.val.length := by
  cases htake : state_only_private_openings.Cursor.take cursor 2#usize with
  | fail error =>
      simp [state_only_private_openings.Cursor.u16, htake] at hu16
  | div =>
      simp [state_only_private_openings.Cursor.u16, htake] at hu16
  | ok output =>
      rcases output with ⟨inner, afterTake⟩
      cases inner with
      | Err error =>
          simp [state_only_private_openings.Cursor.u16, htake,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hu16
      | Ok taken =>
          have hinv := cursor_take_success_inversion cursor 2#usize taken
            afterTake htake
          have htakenlen : taken.val.length = 2 := by
            rw [hinv.1]
            rw [List.slice_length]
            change min (cursor.bytes.val.length - cursor.position.val)
              (cursor.position.val + 2 - cursor.position.val) = 2
            have hend2 : cursor.position.val + 2 ≤
                cursor.bytes.val.length := by
              simpa using hinv.2.2.2.2
            have hdiff : cursor.position.val + 2 - cursor.position.val = 2 := by
              omega
            rw [hdiff, Nat.min_eq_right]
            omega
          simp [state_only_private_openings.Cursor.u16, htake,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.array.TryFromArrayCopySlice.try_from, htakenlen,
            state_only_private_openings.unwrap_copy_slice, lift] at hu16
          rcases hu16 with ⟨rfl, rfl⟩
          exact ⟨hinv.2.1, by simpa using hinv.2.2.1,
            by simpa using hinv.2.2.2.2⟩

theorem cursor_u32_success_position_exact
    (cursor : state_only_private_openings.Cursor) (value : Std.U32)
    (next : state_only_private_openings.Cursor)
    (hu32 : state_only_private_openings.Cursor.u32 cursor =
      .ok (.Ok value, next)) :
    next.bytes = cursor.bytes ∧
      next.position.val = cursor.position.val + 4 ∧
      cursor.position.val + 4 ≤ cursor.bytes.val.length := by
  cases htake : state_only_private_openings.Cursor.take cursor 4#usize with
  | fail error =>
      simp [state_only_private_openings.Cursor.u32, htake] at hu32
  | div =>
      simp [state_only_private_openings.Cursor.u32, htake] at hu32
  | ok output =>
      rcases output with ⟨inner, afterTake⟩
      cases inner with
      | Err error =>
          simp [state_only_private_openings.Cursor.u32, htake,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hu32
      | Ok taken =>
          have hinv := cursor_take_success_inversion cursor 4#usize taken
            afterTake htake
          have htakenlen : taken.val.length = 4 := by
            rw [hinv.1]
            rw [List.slice_length]
            change min (cursor.bytes.val.length - cursor.position.val)
              (cursor.position.val + 4 - cursor.position.val) = 4
            have hend4 : cursor.position.val + 4 ≤
                cursor.bytes.val.length := by
              simpa using hinv.2.2.2.2
            have hdiff : cursor.position.val + 4 - cursor.position.val = 4 := by
              omega
            rw [hdiff, Nat.min_eq_right]
            omega
          simp [state_only_private_openings.Cursor.u32, htake,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.array.TryFromArrayCopySlice.try_from, htakenlen,
            state_only_private_openings.unwrap_copy_slice, lift] at hu32
          rcases hu32 with ⟨rfl, rfl⟩
          exact ⟨hinv.2.1, by simpa using hinv.2.2.1,
            by simpa using hinv.2.2.2.2⟩

theorem checked_section_len_success_inversion
    (count width product : Std.Usize)
    (hsection : state_only_private_openings.checked_section_len count width =
      .ok (.Ok product)) :
    product.val = count.val * width.val ∧
      count.val * width.val ≤ Std.Usize.max := by
  unfold state_only_private_openings.checked_section_len at hsection
  cases hchecked : Std.Usize.checked_mul count width with
  | none =>
      simp [hchecked, lift, core.option.Option.ok_or] at hsection
  | some value =>
      have hmul := Std.Usize.checked_mul_bv_spec count width
      simp [hchecked] at hmul
      simp [hchecked, lift, core.option.Option.ok_or] at hsection
      subst product
      exact ⟨hmul.2.1, hmul.1⟩

def ExactRawParserOutput
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8) : Prop :=
  ∃ frontierCount : Nat,
    opening.count.val = expectedCount.val ∧
    opening.value_width = valueWidth ∧
    opening.offsets.count.val = 0 ∧
    opening.offsets.records.val = 2 ∧
    opening.records.val = List.slice 2
      (2 + expectedCount.val * (valueWidth.val + 32)) proofBytes.val ∧
    opening.records.val.length =
      expectedCount.val * (valueWidth.val + 32) ∧
    opening.offsets.frontier_count.val =
      2 + expectedCount.val * (valueWidth.val + 32) ∧
    opening.offsets.frontier.val =
      2 + expectedCount.val * (valueWidth.val + 32) + 4 ∧
    opening.frontier.val = List.slice
      (2 + expectedCount.val * (valueWidth.val + 32) + 4)
      (2 + expectedCount.val * (valueWidth.val + 32) + 4 +
        frontierCount * 32) proofBytes.val ∧
    opening.frontier.val.length = frontierCount * 32 ∧
    opening.offsets.end.val =
      2 + expectedCount.val * (valueWidth.val + 32) + 4 +
        frontierCount * 32 ∧
    opening.offsets.end.val ≤ proofBytes.val.length ∧
    remainder.val = proofBytes.val.drop opening.offsets.end.val

theorem parse_private_opening_success_exact
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (hparse : state_only_private_openings.parse_private_opening_from_proof
      proofBytes expectedCount valueWidth = .ok (.Ok (opening, remainder))) :
    ExactRawParserOutput proofBytes expectedCount valueWidth opening remainder := by
  cases hrecord : Std.Usize.checked_add valueWidth
      state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES with
  | none =>
      simp [state_only_private_openings.parse_private_opening_from_proof,
        hrecord, lift, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hparse
  | some recordWidth =>
      have hrecordSpec := Std.Usize.checked_add_bv_spec valueWidth
        state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES
      simp [hrecord] at hrecordSpec
      let cursor0 : state_only_private_openings.Cursor :=
        { bytes := proofBytes, position := 0#usize }
      cases hu16 : state_only_private_openings.Cursor.u16 cursor0 with
      | fail error =>
          simp [state_only_private_openings.parse_private_opening_from_proof,
            hrecord, lift, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            state_only_private_openings.Cursor.new, cursor0, hu16] at hparse
      | div =>
          simp [state_only_private_openings.parse_private_opening_from_proof,
            hrecord, lift, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            state_only_private_openings.Cursor.new, cursor0, hu16] at hparse
      | ok countOutput =>
          rcases countOutput with ⟨countResult, cursor1⟩
          cases countResult with
          | Err error =>
              simp [state_only_private_openings.parse_private_opening_from_proof,
                hrecord, lift, core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                state_only_private_openings.Cursor.new, cursor0, hu16] at hparse
          | Ok countWord =>
              let actualCount : Std.Usize :=
                core.convert.num.FromUsizeU16.from countWord
              by_cases hcount : actualCount.val = expectedCount.val
              · have hcountWord : countWord.val = expectedCount.val := by
                  simpa [actualCount] using hcount
                simp [state_only_private_openings.parse_private_opening_from_proof,
                  hrecord, lift, core.option.Option.ok_or,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  state_only_private_openings.Cursor.new, cursor0, hu16,
                  hcountWord] at hparse
                cases hrecordsLen :
                    state_only_private_openings.checked_section_len
                      actualCount recordWidth with
                | fail error =>
                    simp [state_only_private_openings.parse_private_opening_from_proof,
                      hrecord, lift, core.option.Option.ok_or,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      state_only_private_openings.Cursor.new, cursor0, hu16,
                      actualCount, hcount, hrecordsLen] at hparse
                | div =>
                    simp [state_only_private_openings.parse_private_opening_from_proof,
                      hrecord, lift, core.option.Option.ok_or,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      state_only_private_openings.Cursor.new, cursor0, hu16,
                      actualCount, hcount, hrecordsLen] at hparse
                | ok recordsLenResult =>
                    cases recordsLenResult with
                    | Err error =>
                        simp [state_only_private_openings.parse_private_opening_from_proof,
                          hrecord, lift, core.option.Option.ok_or,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          state_only_private_openings.Cursor.new, cursor0, hu16,
                          actualCount, hcount, hrecordsLen] at hparse
                    | Ok recordsLen =>
                        cases hrecordsTake :
                            state_only_private_openings.Cursor.take cursor1 recordsLen with
                        | fail error =>
                            simp [state_only_private_openings.parse_private_opening_from_proof,
                              hrecord, lift, core.option.Option.ok_or,
                              core.result.Result.Insts.CoreOpsTry.branch,
                              state_only_private_openings.Cursor.new, cursor0, hu16,
                              actualCount, hcount, hrecordsLen,
                              hrecordsTake] at hparse
                        | div =>
                            simp [state_only_private_openings.parse_private_opening_from_proof,
                              hrecord, lift, core.option.Option.ok_or,
                              core.result.Result.Insts.CoreOpsTry.branch,
                              state_only_private_openings.Cursor.new, cursor0, hu16,
                              actualCount, hcount, hrecordsLen,
                              hrecordsTake] at hparse
                        | ok recordsOutput =>
                            rcases recordsOutput with ⟨recordsResult, cursor2⟩
                            cases recordsResult with
                            | Err error =>
                                simp [state_only_private_openings.parse_private_opening_from_proof,
                                  hrecord, lift, core.option.Option.ok_or,
                                  core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  state_only_private_openings.Cursor.new, cursor0, hu16,
                                  actualCount, hcount, hrecordsLen,
                                  hrecordsTake] at hparse
                            | Ok records =>
                                cases hu32 :
                                    state_only_private_openings.Cursor.u32 cursor2 with
                                | fail error =>
                                    simp [state_only_private_openings.parse_private_opening_from_proof,
                                      hrecord, lift, core.option.Option.ok_or,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      state_only_private_openings.Cursor.new, cursor0, hu16,
                                      actualCount, hcount, hrecordsLen,
                                      hrecordsTake, hu32] at hparse
                                | div =>
                                    simp [state_only_private_openings.parse_private_opening_from_proof,
                                      hrecord, lift, core.option.Option.ok_or,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      state_only_private_openings.Cursor.new, cursor0, hu16,
                                      actualCount, hcount, hrecordsLen,
                                      hrecordsTake, hu32] at hparse
                                | ok frontierCountOutput =>
                                    rcases frontierCountOutput with
                                      ⟨frontierCountResult, cursor3⟩
                                    cases frontierCountResult with
                                    | Err error =>
                                        simp [state_only_private_openings.parse_private_opening_from_proof,
                                          hrecord, lift, core.option.Option.ok_or,
                                          core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          state_only_private_openings.Cursor.new, cursor0, hu16,
                                          actualCount, hcount, hrecordsLen,
                                          hrecordsTake, hu32] at hparse
                                    | Ok frontierCountWord =>
                                        let frontierCount : Std.Usize :=
                                          UScalar.cast .Usize frontierCountWord
                                        cases hfrontierLen :
                                            state_only_private_openings.checked_section_len
                                              frontierCount 32#usize with
                                        | fail error =>
                                            simp [state_only_private_openings.parse_private_opening_from_proof,
                                              hrecord, lift, core.option.Option.ok_or,
                                              core.result.Result.Insts.CoreOpsTry.branch,
                                              state_only_private_openings.Cursor.new, cursor0, hu16,
                                              actualCount, hcount, hrecordsLen,
                                              hrecordsTake, hu32, frontierCount,
                                              hfrontierLen] at hparse
                                        | div =>
                                            simp [state_only_private_openings.parse_private_opening_from_proof,
                                              hrecord, lift, core.option.Option.ok_or,
                                              core.result.Result.Insts.CoreOpsTry.branch,
                                              state_only_private_openings.Cursor.new, cursor0, hu16,
                                              actualCount, hcount, hrecordsLen,
                                              hrecordsTake, hu32, frontierCount,
                                              hfrontierLen] at hparse
                                        | ok frontierLenResult =>
                                            cases frontierLenResult with
                                            | Err error =>
                                                simp [state_only_private_openings.parse_private_opening_from_proof,
                                                  hrecord, lift, core.option.Option.ok_or,
                                                  core.result.Result.Insts.CoreOpsTry.branch,
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                  state_only_private_openings.Cursor.new, cursor0, hu16,
                                                  actualCount, hcount, hrecordsLen,
                                                  hrecordsTake, hu32, frontierCount,
                                                  hfrontierLen] at hparse
                                            | Ok frontierLen =>
                                                cases hfrontierTake :
                                                    state_only_private_openings.Cursor.take
                                                      cursor3 frontierLen with
                                                | fail error =>
                                                    simp [state_only_private_openings.parse_private_opening_from_proof,
                                                      hrecord, lift, core.option.Option.ok_or,
                                                      core.result.Result.Insts.CoreOpsTry.branch,
                                                      state_only_private_openings.Cursor.new, cursor0, hu16,
                                                      actualCount, hcount, hrecordsLen,
                                                      hrecordsTake, hu32, frontierCount,
                                                      hfrontierLen, hfrontierTake] at hparse
                                                | div =>
                                                    simp [state_only_private_openings.parse_private_opening_from_proof,
                                                      hrecord, lift, core.option.Option.ok_or,
                                                      core.result.Result.Insts.CoreOpsTry.branch,
                                                      state_only_private_openings.Cursor.new, cursor0, hu16,
                                                      actualCount, hcount, hrecordsLen,
                                                      hrecordsTake, hu32, frontierCount,
                                                      hfrontierLen, hfrontierTake] at hparse
                                                | ok frontierOutput =>
                                                    rcases frontierOutput with
                                                      ⟨frontierResult, cursor4⟩
                                                    cases frontierResult with
                                                    | Err error =>
                                                        simp [state_only_private_openings.parse_private_opening_from_proof,
                                                          hrecord, lift, core.option.Option.ok_or,
                                                          core.result.Result.Insts.CoreOpsTry.branch,
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                          state_only_private_openings.Cursor.new, cursor0, hu16,
                                                          actualCount, hcount, hrecordsLen,
                                                          hrecordsTake, hu32, frontierCount,
                                                          hfrontierLen, hfrontierTake] at hparse
                                                    | Ok frontier =>
                                                        have hu16Inv :=
                                                          cursor_u16_success_position_exact
                                                            cursor0 countWord cursor1 hu16
                                                        have hrecordsLenInv :=
                                                          checked_section_len_success_inversion
                                                            actualCount recordWidth recordsLen
                                                            hrecordsLen
                                                        have hrecordsInv :=
                                                          cursor_take_success_inversion
                                                            cursor1 recordsLen records cursor2
                                                            hrecordsTake
                                                        have hu32Inv :=
                                                          cursor_u32_success_position_exact
                                                            cursor2 frontierCountWord cursor3 hu32
                                                        have hfrontierLenInv :=
                                                          checked_section_len_success_inversion
                                                            frontierCount 32#usize frontierLen
                                                            hfrontierLen
                                                        have hfrontierInv :=
                                                          cursor_take_success_inversion
                                                            cursor3 frontierLen frontier cursor4
                                                            hfrontierTake
                                                        have hcursor3Bytes :
                                                            cursor3.bytes = proofBytes := by
                                                          calc
                                                            cursor3.bytes = cursor2.bytes := hu32Inv.1
                                                            _ = cursor1.bytes := hrecordsInv.2.1
                                                            _ = cursor0.bytes := hu16Inv.1
                                                            _ = proofBytes := rfl
                                                        have hend : cursor4.position.val ≤
                                                            proofBytes.val.length := by
                                                          have h := hfrontierInv.2.2.2.2
                                                          rw [hcursor3Bytes] at h
                                                          omega
                                                        simp [state_only_private_openings.parse_private_opening_from_proof,
                                                          hrecord, lift, core.option.Option.ok_or,
                                                          core.result.Result.Insts.CoreOpsTry.branch,
                                                          state_only_private_openings.Cursor.new, cursor0, hu16,
                                                          actualCount, hcount, hrecordsLen,
                                                          hrecordsTake, hu32, frontierCount,
                                                          hfrontierLen, hfrontierTake,
                                                          core.slice.index.Slice.index,
                                                          core.slice.index.SliceIndexRangeFromUsizeSlice.index,
                                                          hend] at hparse
                                                        rcases hparse with ⟨rfl, rfl⟩
                                                        have hrecordWidthVal :
                                                            recordWidth.val = valueWidth.val + 32 := by
                                                          simpa [state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]
                                                            using hrecordSpec.2.1
                                                        have hrecordsLenVal : recordsLen.val =
                                                            expectedCount.val * (valueWidth.val + 32) := by
                                                          calc
                                                            recordsLen.val = actualCount.val *
                                                                recordWidth.val := hrecordsLenInv.1
                                                            _ = expectedCount.val *
                                                                (valueWidth.val + 32) := by
                                                                  rw [hcount, hrecordWidthVal]
                                                        have hcursor1Pos : cursor1.position.val = 2 := by
                                                          simpa [cursor0] using hu16Inv.2.1
                                                        have hcursor1Bytes : cursor1.bytes = proofBytes := by
                                                          simpa [cursor0] using hu16Inv.1
                                                        have hrecordsVal : records.val = List.slice 2
                                                            (2 + expectedCount.val *
                                                              (valueWidth.val + 32)) proofBytes.val := by
                                                          simpa [hcursor1Pos, hcursor1Bytes,
                                                            hrecordsLenVal] using hrecordsInv.1
                                                        have hrecordsLength : records.val.length =
                                                            expectedCount.val *
                                                              (valueWidth.val + 32) := by
                                                          have h := cursor_take_success_length_exact
                                                            cursor1 recordsLen records cursor2
                                                            hrecordsTake
                                                          simpa [hrecordsLenVal] using h
                                                        have hcursor2Pos : cursor2.position.val =
                                                            2 + expectedCount.val *
                                                              (valueWidth.val + 32) := by
                                                          calc
                                                            cursor2.position.val = cursor1.position.val +
                                                                recordsLen.val := hrecordsInv.2.2.1
                                                            _ = 2 + expectedCount.val *
                                                                (valueWidth.val + 32) := by
                                                                  rw [hcursor1Pos, hrecordsLenVal]
                                                        have hcursor3Pos : cursor3.position.val =
                                                            2 + expectedCount.val *
                                                              (valueWidth.val + 32) + 4 := by
                                                          calc
                                                            cursor3.position.val = cursor2.position.val + 4 :=
                                                              hu32Inv.2.1
                                                            _ = 2 + expectedCount.val *
                                                                (valueWidth.val + 32) + 4 := by
                                                                  rw [hcursor2Pos]
                                                        have hfrontierLenVal : frontierLen.val =
                                                            frontierCount.val * 32 := by
                                                          simpa using hfrontierLenInv.1
                                                        have hfrontierVal : frontier.val = List.slice
                                                            (2 + expectedCount.val *
                                                              (valueWidth.val + 32) + 4)
                                                            (2 + expectedCount.val *
                                                              (valueWidth.val + 32) + 4 +
                                                                frontierCount.val * 32) proofBytes.val := by
                                                          simpa [hcursor3Pos, hcursor3Bytes,
                                                            hfrontierLenVal] using hfrontierInv.1
                                                        have hfrontierLength : frontier.val.length =
                                                            frontierCount.val * 32 := by
                                                          have h := cursor_take_success_length_exact
                                                            cursor3 frontierLen frontier cursor4
                                                            hfrontierTake
                                                          simpa [hfrontierLenVal] using h
                                                        have hcursor4Pos : cursor4.position.val =
                                                            2 + expectedCount.val *
                                                              (valueWidth.val + 32) + 4 +
                                                                frontierCount.val * 32 := by
                                                          calc
                                                            cursor4.position.val = cursor3.position.val +
                                                                frontierLen.val := hfrontierInv.2.2.1
                                                            _ = 2 + expectedCount.val *
                                                                (valueWidth.val + 32) + 4 +
                                                                  frontierCount.val * 32 := by
                                                                    rw [hcursor3Pos,
                                                                      hfrontierLenVal]
                                                        unfold ExactRawParserOutput
                                                        refine ⟨frontierCount.val, hcount, rfl, rfl,
                                                          hcursor1Pos, hrecordsVal, hrecordsLength,
                                                          hcursor2Pos, hcursor3Pos, hfrontierVal,
                                                          hfrontierLength, hcursor4Pos, hend, ?_⟩
                                                        rfl
              · have hcountWord : countWord.val ≠ expectedCount.val := by
                  simpa [actualCount] using hcount
                simp [state_only_private_openings.parse_private_opening_from_proof,
                  hrecord, lift, core.option.Option.ok_or,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  state_only_private_openings.Cursor.new, cursor0, hu16,
                  actualCount, hcount, hcountWord] at hparse

/-! ## From the extracted raw slices to the maintained opening view -/

def parserU8ToByte (byte : Std.U8) :
    AspisV5ComponentCQM31Representation.Byte :=
  ⟨byte.val, by
    have h := UScalar.hBounds byte
    norm_num at h ⊢
    exact h⟩

def generatedParserOpeningToReturned
    (opening : state_only_private_openings.StateOnlyPrivateOpening) :
    ReturnedOpening where
  count := opening.count.val
  valueWidth := opening.value_width.val
  records := opening.records.val.map parserU8ToByte
  frontier := opening.frontier.val.map parserU8ToByte
  offsets :=
    { count := opening.offsets.count.val
      records := opening.offsets.records.val
      frontierCount := opening.offsets.frontier_count.val
      frontier := opening.offsets.frontier.val
      endOffset := opening.offsets.end.val }

/-- The only byte-identification facts needed after the already-proved raw
parser theorem: the two returned slices are the record and frontier portions
of the authenticated section. -/
structure ExtractedParserSlicesMatchTrace
    {sha256 tree root queries}
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (trace : ExactSectionTrace sha256 tree root queries) : Prop where
  records : opening.records.val.map parserU8ToByte = trace.records.flatten
  frontier : opening.frontier.val.map parserU8ToByte =
    flattenDigests trace.frontier

private theorem map_parserU8ToByte_slice
    (start stop : Nat) (bytes : List Std.U8) :
    (List.slice start stop bytes).map parserU8ToByte =
      List.slice start stop (bytes.map parserU8ToByte) := by
  simp [List.slice]

private theorem slice_append_middle {A : Type}
    (before middle after : List A) :
    List.slice before.length (before.length + middle.length)
        (before ++ middle ++ after) = middle := by
  simp [List.slice]

/-- The two slice-identification facts follow from a wire prefix and the
length of the parsed frontier.  No byte-by-byte slice equality must be
supplied separately. -/
theorem exactRawParserOutput_slicesMatchTrace_of_wirePrefix
    {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (hraw : ExactRawParserOutput proofBytes expectedCount valueWidth
      opening remainder)
    (hcount : expectedCount.val = trace.records.length)
    (hwidth : valueWidth.val = AspisV5MerkleAuthenticationBinding.valueWidth tree)
    (suffix : List AspisV5ComponentCQM31Representation.Byte)
    (hwire : proofBytes.val.map parserU8ToByte = trace.wire ++ suffix)
    (hfrontierLength : opening.frontier.val.length =
      (flattenDigests trace.frontier).length) :
    ExtractedParserSlicesMatchTrace opening trace := by
  rcases hraw with ⟨frontierCount, _hopenCount, _hopenWidth, _hoffsetCount,
    _hoffsetRecords, hrecordsSlice, _hrecordsLength,
    _hoffsetFrontierCount, _hoffsetFrontier, hfrontierSlice,
    hrawFrontierLength, _hoffsetEnd, _hend, _hremainder⟩
  have htraceRecordsLength :
      trace.records.flatten.length =
        trace.records.length *
          (AspisV5MerkleAuthenticationBinding.valueWidth tree + 32) := by
    rw [List.length_flatten]
    have hlengths : trace.records.map List.length =
        List.replicate trace.records.length
          (AspisV5MerkleAuthenticationBinding.valueWidth tree + 32) := by
      apply List.eq_replicate_iff.mpr
      constructor
      · simp
      · intro value hvalue
        simp only [List.mem_map] at hvalue
        obtain ⟨record, hrecord, rfl⟩ := hvalue
        exact exactSection_records_uniform_length trace record hrecord
    rw [hlengths, List.sum_replicate]
    simp
  have hrecordsBytes :
      expectedCount.val * (valueWidth.val + 32) =
        trace.records.flatten.length := by
    calc
      expectedCount.val * (valueWidth.val + 32) =
          trace.records.length *
            (AspisV5MerkleAuthenticationBinding.valueWidth tree + 32) := by
        rw [hcount, hwidth]
      _ = trace.records.flatten.length := htraceRecordsLength.symm
  have hfrontierCount : frontierCount = trace.frontier.length := by
    rw [hfrontierLength, flattenDigests_length] at hrawFrontierLength
    omega
  constructor
  · rw [hrecordsSlice, map_parserU8ToByte_slice, hwire,
      openingOfTrace_wire_exact trace]
    have hmiddle := slice_append_middle
      (u16LE (openingOfTrace trace).count)
      (openingOfTrace trace).records
      (u32LE trace.frontier.length ++
        (openingOfTrace trace).frontier ++ suffix)
    simpa [openingOfTrace_count, openingOfTrace_records, u16LE_length,
      hrecordsBytes, List.append_assoc] using hmiddle
  · rw [hfrontierSlice, map_parserU8ToByte_slice, hwire,
      openingOfTrace_wire_exact trace]
    have hmiddle := slice_append_middle
      (u16LE (openingOfTrace trace).count ++
        (openingOfTrace trace).records ++ u32LE trace.frontier.length)
      (openingOfTrace trace).frontier suffix
    simpa [openingOfTrace_count, openingOfTrace_records,
      openingOfTrace_frontier, u16LE_length, u32LE_length,
      hrecordsBytes, hfrontierCount, flattenDigests_length,
      List.append_assoc, Nat.mul_comm, Nat.add_assoc] using hmiddle

/-- A successful extracted parser output, once its two zero-copy slices are
identified with one authenticated section, is exactly `openingOfTrace`,
including every offset. -/
theorem exactRawParserOutput_to_openingOfTrace
    {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (hraw : ExactRawParserOutput proofBytes expectedCount valueWidth
      opening remainder)
    (hcount : expectedCount.val = trace.records.length)
    (hwidth : valueWidth.val = AspisV5MerkleAuthenticationBinding.valueWidth tree)
    (hslices : ExtractedParserSlicesMatchTrace opening trace) :
    generatedParserOpeningToReturned opening = openingOfTrace trace := by
  rcases hraw with ⟨frontierCount, hopenCount, hopenWidth, hoffsetCount,
    hoffsetRecords, _hrecordsSlice, hrecordsLength, hoffsetFrontierCount,
    hoffsetFrontier, _hfrontierSlice, hfrontierLength, hoffsetEnd,
    _hend, _hremainder⟩
  have hrecordsMappedLength :
      (opening.records.val.map parserU8ToByte).length =
        expectedCount.val * (valueWidth.val + 32) := by
    simpa using hrecordsLength
  have hfrontierMappedLength :
      (opening.frontier.val.map parserU8ToByte).length =
        frontierCount * 32 := by
    simpa using hfrontierLength
  have hfrontierCount : frontierCount = trace.frontier.length := by
    have hmapped : frontierCount * 32 =
        (flattenDigests trace.frontier).length := by
      rw [← hslices.frontier, hfrontierMappedLength]
    rw [flattenDigests_length] at hmapped
    omega
  have hrecordsBytes :
      expectedCount.val * (valueWidth.val + 32) =
        trace.records.flatten.length := by
    rw [← hrecordsMappedLength, hslices.records]
  unfold generatedParserOpeningToReturned openingOfTrace
  simp only [ReturnedOpening.mk.injEq, OpeningOffsets.mk.injEq]
  refine ⟨hopenCount.trans hcount, congrArg UScalar.val hopenWidth |>.trans hwidth,
    hslices.records, hslices.frontier, ?_⟩
  refine ⟨hoffsetCount, hoffsetRecords, ?_, ?_, ?_⟩
  · calc
      opening.offsets.frontier_count.val =
          2 + expectedCount.val * (valueWidth.val + 32) :=
        hoffsetFrontierCount
      _ = 2 + trace.records.flatten.length := by rw [hrecordsBytes]
  · calc
      opening.offsets.frontier.val =
          2 + expectedCount.val * (valueWidth.val + 32) + 4 :=
        hoffsetFrontier
      _ = 2 + trace.records.flatten.length + 4 := by rw [hrecordsBytes]
  · calc
      opening.offsets.end.val =
          2 + expectedCount.val * (valueWidth.val + 32) + 4 +
            frontierCount * 32 := hoffsetEnd
      _ = 2 + trace.records.flatten.length + 4 +
          (flattenDigests trace.frontier).length := by
        rw [hrecordsBytes, hfrontierCount, flattenDigests_length]
        omega

/-- A directly composable form for the outer five-section driver: an exact
raw parse of a section whose converted bytes begin with the authenticated wire
returns exactly that authenticated opening.  The only extra scalar fact is
that the parsed frontier has the authenticated frontier's byte length. -/
theorem exactRawParserOutput_to_openingOfTrace_of_wirePrefix
    {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (hraw : ExactRawParserOutput proofBytes expectedCount valueWidth
      opening remainder)
    (hcount : expectedCount.val = trace.records.length)
    (hwidth : valueWidth.val = AspisV5MerkleAuthenticationBinding.valueWidth tree)
    (suffix : List AspisV5ComponentCQM31Representation.Byte)
    (hwire : proofBytes.val.map parserU8ToByte = trace.wire ++ suffix)
    (hfrontierLength : opening.frontier.val.length =
      (flattenDigests trace.frontier).length) :
    generatedParserOpeningToReturned opening = openingOfTrace trace := by
  apply exactRawParserOutput_to_openingOfTrace trace proofBytes expectedCount
    valueWidth opening remainder hraw hcount hwidth
  exact exactRawParserOutput_slicesMatchTrace_of_wirePrefix trace proofBytes
    expectedCount valueWidth opening remainder hraw hcount hwidth suffix hwire
    hfrontierLength

#print axioms usize_checked_add_eq_some
#print axioms usize_checked_mul_eq_some
#print axioms cursor_take_success_exact
#print axioms cursor_take_success_inversion
#print axioms cursor_u16_success_position_exact
#print axioms cursor_u32_success_position_exact
#print axioms checked_section_len_success_inversion
#print axioms parse_private_opening_success_exact
#print axioms exactRawParserOutput_slicesMatchTrace_of_wirePrefix
#print axioms exactRawParserOutput_to_openingOfTrace
#print axioms exactRawParserOutput_to_openingOfTrace_of_wirePrefix

end AspisV5OpeningParserSourceProof
