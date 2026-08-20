import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullParserBridge
import V5MerkleUnchangedFullHelperBridge

/-! The successful production parser consumes exactly the maintained
little-endian section encoding. -/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000
set_option linter.unusedSimpArgs false

namespace AspisV5MerkleUnchangedFullWireCanonicality

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullParserBridge

abbrev generatedU8ToByte :=
  AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte

theorem u16_from_le_bytes_exact
    (bytes : Array Std.U8 2#usize) :
    bytes.val.map generatedU8ToByte =
      u16LE (core.num.U16.from_le_bytes bytes).val := by
  rcases bytes with ⟨bytes, hlength⟩
  simp only [OfNat.ofNat, OfScientific.ofScientific] at hlength
  have hshape : ∃ b0 b1, bytes = [b0, b1] := by
    match bytes with
    | [b0, b1] => exact ⟨b0, b1, rfl⟩
    | [] => simp at hlength
    | [_] => simp at hlength
    | b0 :: b1 :: _ :: tail =>
        have : False := by simpa using hlength
        contradiction
  rcases hshape with ⟨b0, b1, rfl⟩
  have hdecoded :
      (core.num.U16.from_le_bytes
        (⟨[b0, b1], by simp⟩ : Array Std.U8 2#usize)).val =
        b0.val + 256 * b1.val := by
    simp only [core.num.U16.from_le_bytes, UScalar.val,
      BitVec.toNat_cast, BitVec.fromLEBytes, List.map]
    simp [BitVec.toNat_or, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft]
    have hb0 := UScalar.hBounds b0
    have hb1 := UScalar.hBounds b1
    norm_num at hb0 hb1
    rw [Nat.mod_eq_of_lt (by omega : b0.val < 65536)]
    rw [Nat.mod_eq_of_lt (by omega : b1.val < 65536)]
    rw [Nat.mod_eq_of_lt (by
      simp only [Nat.shiftLeft_eq]
      omega : b1.val <<< 8 < 65536)]
    rw [Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega) b1.val]
    simp [Nat.shiftLeft_eq]
    omega
  rw [hdecoded]
  simp only [List.map, u16LE]
  congr 1
  · apply Fin.ext
    simp only [AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte,
      littleEndianByte]
    simp only [pow_zero, Nat.div_one]
    change b0.val = (b0.val + 256 * b1.val) % 256
    have hb0 := UScalar.hBounds b0
    norm_num at hb0
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb0]
  · congr 1
    apply Fin.ext
    simp only [AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte,
      littleEndianByte]
    simp only [pow_one]
    change b1.val = ((b0.val + 256 * b1.val) / 256) % 256
    have hb0 := UScalar.hBounds b0
    have hb1 := UScalar.hBounds b1
    norm_num at hb0 hb1
    rw [Nat.add_mul_div_left _ _ (by norm_num),
      Nat.div_eq_of_lt hb0, Nat.zero_add, Nat.mod_eq_of_lt hb1]

theorem u32_from_le_bytes_exact
    (bytes : Array Std.U8 4#usize) :
    bytes.val.map generatedU8ToByte =
      u32LE (core.num.U32.from_le_bytes bytes).val := by
  rcases bytes with ⟨bytes, hlength⟩
  simp only [OfNat.ofNat, OfScientific.ofScientific] at hlength
  have hshape : ∃ b0 b1 b2 b3, bytes = [b0, b1, b2, b3] := by
    match bytes with
    | [b0, b1, b2, b3] => exact ⟨b0, b1, b2, b3, rfl⟩
    | [] => simp at hlength
    | [_] => simp at hlength
    | [_, _] => simp at hlength
    | [_, _, _] => simp at hlength
    | b0 :: b1 :: b2 :: b3 :: tail =>
        have htail : tail = [] := by simpa using hlength
        subst tail
        exact ⟨b0, b1, b2, b3, rfl⟩
  rcases hshape with ⟨b0, b1, b2, b3, rfl⟩
  have hdecoded :
      (core.num.U32.from_le_bytes
        (⟨[b0, b1, b2, b3], by simp⟩ : Array Std.U8 4#usize)).val =
        b0.val + 256 * b1.val + 65536 * b2.val +
          16777216 * b3.val := by
    simp only [core.num.U32.from_le_bytes, UScalar.val,
      BitVec.toNat_cast, BitVec.fromLEBytes, List.map]
    simp [BitVec.toNat_or, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft]
    have hb0 := UScalar.hBounds b0
    have hb1 := UScalar.hBounds b1
    have hb2 := UScalar.hBounds b2
    have hb3 := UScalar.hBounds b3
    norm_num at hb0 hb1 hb2 hb3
    have h23 :
        b2.val % 16777216 |||
          (((b3.val % 65536) <<< 8) % 65536) % 16777216 =
            b2.val + 256 * b3.val := by
      rw [Nat.mod_eq_of_lt (by omega : b2.val < 16777216)]
      rw [Nat.mod_eq_of_lt (by omega : b3.val < 65536)]
      rw [Nat.mod_eq_of_lt (by
        simp only [Nat.shiftLeft_eq]
        omega : b3.val <<< 8 < 65536)]
      rw [Nat.mod_eq_of_lt (by
        simp only [Nat.shiftLeft_eq]
        omega : b3.val <<< 8 < 16777216)]
      rw [Nat.or_comm,
        ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega) b3.val]
      simp only [Nat.shiftLeft_eq]
      omega
    rw [h23]
    have h123 :
        b1.val % 4294967296 |||
          ((((b2.val + 256 * b3.val) <<< 8) % 16777216) %
            4294967296) =
          b1.val + 256 * b2.val + 65536 * b3.val := by
      rw [Nat.mod_eq_of_lt (by omega : b1.val < 4294967296)]
      rw [Nat.mod_eq_of_lt (by
        simp only [Nat.shiftLeft_eq]
        omega : (b2.val + 256 * b3.val) <<< 8 < 16777216)]
      rw [Nat.mod_eq_of_lt (by
        simp only [Nat.shiftLeft_eq]
        omega : (b2.val + 256 * b3.val) <<< 8 < 4294967296)]
      rw [Nat.or_comm,
        ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega) _]
      simp only [Nat.shiftLeft_eq]
      omega
    rw [h123]
    rw [Nat.mod_eq_of_lt (by omega : b0.val < 4294967296)]
    rw [Nat.mod_eq_of_lt (by
      simp only [Nat.shiftLeft_eq]
      omega :
        (b1.val + 256 * b2.val + 65536 * b3.val) <<< 8 <
          4294967296)]
    rw [Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega) _]
    simp only [Nat.shiftLeft_eq]
    omega
  rw [hdecoded]
  simp only [List.map, u32LE]
  congr 1
  · apply Fin.ext
    simp only [AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte,
      littleEndianByte, pow_zero, Nat.div_one]
    have hb0 := UScalar.hBounds b0
    norm_num at hb0
    omega
  · congr 1
    · apply Fin.ext
      simp only [AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte,
        littleEndianByte, pow_one]
      have hb0 := UScalar.hBounds b0
      have hb1 := UScalar.hBounds b1
      norm_num at hb0 hb1
      omega
    · congr 1
      · apply Fin.ext
        simp only [AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte,
          littleEndianByte]
        have hb0 := UScalar.hBounds b0
        have hb1 := UScalar.hBounds b1
        have hb2 := UScalar.hBounds b2
        norm_num at hb0 hb1 hb2
        omega
      · congr 1
        apply Fin.ext
        simp only [AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte,
          littleEndianByte]
        have hb0 := UScalar.hBounds b0
        have hb1 := UScalar.hBounds b1
        have hb2 := UScalar.hBounds b2
        have hb3 := UScalar.hBounds b3
        norm_num at hb0 hb1 hb2 hb3
        omega

theorem cursor_u16_success_bytes_exact
    (cursor : aspis_core.state_only_private_openings.Cursor) (value : Std.U16)
    (next : aspis_core.state_only_private_openings.Cursor)
    (hu16 : aspis_core.state_only_private_openings.Cursor.u16 cursor =
      .ok (.Ok value, next)) :
    (List.slice cursor.position.val (cursor.position.val + 2)
        cursor.bytes.val).map generatedU8ToByte = u16LE value.val := by
  cases htake : aspis_core.state_only_private_openings.Cursor.take cursor 2#usize with
  | fail error =>
      simp [aspis_core.state_only_private_openings.Cursor.u16, htake] at hu16
  | div =>
      simp [aspis_core.state_only_private_openings.Cursor.u16, htake] at hu16
  | ok output =>
      rcases output with ⟨inner, afterTake⟩
      cases inner with
      | Err error =>
          simp [aspis_core.state_only_private_openings.Cursor.u16, htake,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hu16
      | Ok taken =>
          have hinv := cursor_take_success_inversion cursor 2#usize taken
            afterTake htake
          have htakenlen : taken.val.length = 2 := by
            exact cursor_take_success_length_exact cursor 2#usize taken
              afterTake htake
          simp [aspis_core.state_only_private_openings.Cursor.u16, htake,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.array.TryFromArrayCopySlice.try_from, htakenlen,
            core.result.Result.unwrap, lift] at hu16
          rcases hu16 with ⟨rfl, rfl⟩
          have hslice : List.slice cursor.position.val
              (cursor.position.val + 2) cursor.bytes.val = taken.val := by
            simpa using hinv.1.symm
          rw [hslice]
          exact u16_from_le_bytes_exact ⟨taken.val, by simpa using htakenlen⟩

theorem cursor_u32_success_bytes_exact
    (cursor : aspis_core.state_only_private_openings.Cursor) (value : Std.U32)
    (next : aspis_core.state_only_private_openings.Cursor)
    (hu32 : aspis_core.state_only_private_openings.Cursor.u32 cursor =
      .ok (.Ok value, next)) :
    (List.slice cursor.position.val (cursor.position.val + 4)
        cursor.bytes.val).map generatedU8ToByte = u32LE value.val := by
  cases htake : aspis_core.state_only_private_openings.Cursor.take cursor 4#usize with
  | fail error =>
      simp [aspis_core.state_only_private_openings.Cursor.u32, htake] at hu32
  | div =>
      simp [aspis_core.state_only_private_openings.Cursor.u32, htake] at hu32
  | ok output =>
      rcases output with ⟨inner, afterTake⟩
      cases inner with
      | Err error =>
          simp [aspis_core.state_only_private_openings.Cursor.u32, htake,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hu32
      | Ok taken =>
          have hinv := cursor_take_success_inversion cursor 4#usize taken
            afterTake htake
          have htakenlen : taken.val.length = 4 := by
            exact cursor_take_success_length_exact cursor 4#usize taken
              afterTake htake
          simp [aspis_core.state_only_private_openings.Cursor.u32, htake,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.array.TryFromArrayCopySlice.try_from, htakenlen,
            core.result.Result.unwrap, lift] at hu32
          rcases hu32 with ⟨rfl, rfl⟩
          have hslice : List.slice cursor.position.val
              (cursor.position.val + 4) cursor.bytes.val = taken.val := by
            simpa using hinv.1.symm
          rw [hslice]
          exact u32_from_le_bytes_exact ⟨taken.val, by simpa using htakenlen⟩

def ExactParserHeaderBytes
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening) : Prop :=
  ∃ frontierCount : Nat,
    (List.slice 0 2 proofBytes.val).map generatedU8ToByte =
      u16LE expectedCount.val ∧
    (List.slice
      (2 + expectedCount.val * (valueWidth.val + 32))
      (2 + expectedCount.val * (valueWidth.val + 32) + 4)
      proofBytes.val).map generatedU8ToByte = u32LE frontierCount ∧
    opening.frontier.val.length = frontierCount * 32

theorem parse_private_opening_success_headers
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (hparse : aspis_core.state_only_private_openings.parse_private_opening_from_proof
      proofBytes expectedCount valueWidth = .ok (.Ok (opening, remainder))) :
    ExactParserHeaderBytes proofBytes expectedCount valueWidth opening := by
  cases hrecord : Std.Usize.checked_add valueWidth
      aspis_core.state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES with
  | none =>
      simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
        hrecord, lift, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hparse
  | some recordWidth =>
      have hrecordSpec := Std.Usize.checked_add_bv_spec valueWidth
        aspis_core.state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES
      simp [hrecord] at hrecordSpec
      let cursor0 : aspis_core.state_only_private_openings.Cursor :=
        { bytes := proofBytes, position := 0#usize }
      cases hu16 : aspis_core.state_only_private_openings.Cursor.u16 cursor0 with
      | fail error =>
          simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
            hrecord, lift, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16] at hparse
      | div =>
          simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
            hrecord, lift, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16] at hparse
      | ok countOutput =>
          rcases countOutput with ⟨countResult, cursor1⟩
          cases countResult with
          | Err error =>
              simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                hrecord, lift, core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16] at hparse
          | Ok countWord =>
              let actualCount : Std.Usize :=
                core.convert.num.FromUsizeU16.from countWord
              by_cases hcount : actualCount.val = expectedCount.val
              · have hcountWord : countWord.val = expectedCount.val := by
                  simpa [actualCount] using hcount
                simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                  hrecord, lift, core.option.Option.ok_or,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                  hcountWord] at hparse
                cases hrecordsLen :
                    aspis_core.state_only_private_openings.checked_section_len
                      actualCount recordWidth with
                | fail error =>
                    simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                      hrecord, lift, core.option.Option.ok_or,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                      actualCount, hcount, hrecordsLen] at hparse
                | div =>
                    simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                      hrecord, lift, core.option.Option.ok_or,
                      core.result.Result.Insts.CoreOpsTry.branch,
                      aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                      actualCount, hcount, hrecordsLen] at hparse
                | ok recordsLenResult =>
                    cases recordsLenResult with
                    | Err error =>
                        simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                          hrecord, lift, core.option.Option.ok_or,
                          core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                          actualCount, hcount, hrecordsLen] at hparse
                    | Ok recordsLen =>
                        cases hrecordsTake :
                            aspis_core.state_only_private_openings.Cursor.take cursor1 recordsLen with
                        | fail error =>
                            simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                              hrecord, lift, core.option.Option.ok_or,
                              core.result.Result.Insts.CoreOpsTry.branch,
                              aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                              actualCount, hcount, hrecordsLen,
                              hrecordsTake] at hparse
                        | div =>
                            simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                              hrecord, lift, core.option.Option.ok_or,
                              core.result.Result.Insts.CoreOpsTry.branch,
                              aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                              actualCount, hcount, hrecordsLen,
                              hrecordsTake] at hparse
                        | ok recordsOutput =>
                            rcases recordsOutput with ⟨recordsResult, cursor2⟩
                            cases recordsResult with
                            | Err error =>
                                simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                  hrecord, lift, core.option.Option.ok_or,
                                  core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                  aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                  actualCount, hcount, hrecordsLen,
                                  hrecordsTake] at hparse
                            | Ok records =>
                                cases hu32 :
                                    aspis_core.state_only_private_openings.Cursor.u32 cursor2 with
                                | fail error =>
                                    simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                      hrecord, lift, core.option.Option.ok_or,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                      actualCount, hcount, hrecordsLen,
                                      hrecordsTake, hu32] at hparse
                                | div =>
                                    simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                      hrecord, lift, core.option.Option.ok_or,
                                      core.result.Result.Insts.CoreOpsTry.branch,
                                      aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                      actualCount, hcount, hrecordsLen,
                                      hrecordsTake, hu32] at hparse
                                | ok frontierCountOutput =>
                                    rcases frontierCountOutput with
                                      ⟨frontierCountResult, cursor3⟩
                                    cases frontierCountResult with
                                    | Err error =>
                                        simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                          hrecord, lift, core.option.Option.ok_or,
                                          core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                          actualCount, hcount, hrecordsLen,
                                          hrecordsTake, hu32] at hparse
                                    | Ok frontierCountWord =>
                                        let frontierCount : Std.Usize :=
                                          UScalar.cast .Usize frontierCountWord
                                        cases hfrontierLen :
                                            aspis_core.state_only_private_openings.checked_section_len
                                              frontierCount 32#usize with
                                        | fail error =>
                                            simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                              hrecord, lift, core.option.Option.ok_or,
                                              core.result.Result.Insts.CoreOpsTry.branch,
                                              aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                              actualCount, hcount, hrecordsLen,
                                              hrecordsTake, hu32, frontierCount,
                                              hfrontierLen] at hparse
                                        | div =>
                                            simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                              hrecord, lift, core.option.Option.ok_or,
                                              core.result.Result.Insts.CoreOpsTry.branch,
                                              aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                              actualCount, hcount, hrecordsLen,
                                              hrecordsTake, hu32, frontierCount,
                                              hfrontierLen] at hparse
                                        | ok frontierLenResult =>
                                            cases frontierLenResult with
                                            | Err error =>
                                                simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                                  hrecord, lift, core.option.Option.ok_or,
                                                  core.result.Result.Insts.CoreOpsTry.branch,
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                  aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                                  actualCount, hcount, hrecordsLen,
                                                  hrecordsTake, hu32, frontierCount,
                                                  hfrontierLen] at hparse
                                            | Ok frontierLen =>
                                                cases hfrontierTake :
                                                    aspis_core.state_only_private_openings.Cursor.take
                                                      cursor3 frontierLen with
                                                | fail error =>
                                                    simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                                      hrecord, lift, core.option.Option.ok_or,
                                                      core.result.Result.Insts.CoreOpsTry.branch,
                                                      aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                                      actualCount, hcount, hrecordsLen,
                                                      hrecordsTake, hu32, frontierCount,
                                                      hfrontierLen, hfrontierTake] at hparse
                                                | div =>
                                                    simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                                      hrecord, lift, core.option.Option.ok_or,
                                                      core.result.Result.Insts.CoreOpsTry.branch,
                                                      aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                                      actualCount, hcount, hrecordsLen,
                                                      hrecordsTake, hu32, frontierCount,
                                                      hfrontierLen, hfrontierTake] at hparse
                                                | ok frontierOutput =>
                                                    rcases frontierOutput with
                                                      ⟨frontierResult, cursor4⟩
                                                    cases frontierResult with
                                                    | Err error =>
                                                        simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                                          hrecord, lift, core.option.Option.ok_or,
                                                          core.result.Result.Insts.CoreOpsTry.branch,
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                          aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
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
                                                        simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                                                          hrecord, lift, core.option.Option.ok_or,
                                                          core.result.Result.Insts.CoreOpsTry.branch,
                                                          aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                                                          actualCount, hcount, hrecordsLen,
                                                          hrecordsTake, hu32, frontierCount,
                                                          hfrontierLen, hfrontierTake,
                                                          core.slice.index.Slice.index,
                                                          core.slice.index.SliceIndexRangeFromUsizeSlice.index,
                                                          hend] at hparse
                                                        rcases hparse with ⟨rfl, rfl⟩
                                                        have hrecordWidthVal :
                                                            recordWidth.val = valueWidth.val + 32 := by
                                                          simpa [aspis_core.state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]
                                                            using hrecordSpec.2.1
                                                        have hrecordsLenVal : recordsLen.val =
                                                            expectedCount.val *
                                                              (valueWidth.val + 32) := by
                                                          calc
                                                            recordsLen.val = actualCount.val *
                                                                recordWidth.val := hrecordsLenInv.1
                                                            _ = expectedCount.val *
                                                                (valueWidth.val + 32) := by
                                                                  rw [hcount, hrecordWidthVal]
                                                        have hcursor1Pos : cursor1.position.val = 2 := by
                                                          simpa [cursor0] using hu16Inv.2.1
                                                        have hcursor2Pos : cursor2.position.val =
                                                            2 + expectedCount.val *
                                                              (valueWidth.val + 32) := by
                                                          calc
                                                            cursor2.position.val = cursor1.position.val +
                                                                recordsLen.val := hrecordsInv.2.2.1
                                                            _ = 2 + expectedCount.val *
                                                                (valueWidth.val + 32) := by
                                                                  rw [hcursor1Pos, hrecordsLenVal]
                                                        have hcursor2Bytes :
                                                            cursor2.bytes = proofBytes := by
                                                          calc
                                                            cursor2.bytes = cursor1.bytes := hrecordsInv.2.1
                                                            _ = cursor0.bytes := hu16Inv.1
                                                            _ = proofBytes := rfl
                                                        have hcountBytes :=
                                                          cursor_u16_success_bytes_exact
                                                            cursor0 countWord cursor1 hu16
                                                        have hfrontierBytes :=
                                                          cursor_u32_success_bytes_exact
                                                            cursor2 frontierCountWord cursor3 hu32
                                                        refine ⟨frontierCount.val, ?_, ?_, ?_⟩
                                                        · simpa [cursor0, hcountWord] using hcountBytes
                                                        · have hfrontierCountVal :
                                                              frontierCount.val =
                                                                frontierCountWord.val := by
                                                            simpa [frontierCount] using
                                                              U32.cast_Usize_val_eq frontierCountWord
                                                          simpa [hcursor2Pos, hcursor2Bytes,
                                                            hfrontierCountVal] using hfrontierBytes
                                                        · have hfrontierLength :=
                                                            cursor_take_success_length_exact
                                                              cursor3 frontierLen frontier cursor4
                                                              hfrontierTake
                                                          have hfrontierLenVal : frontierLen.val =
                                                              frontierCount.val * 32 := by
                                                            simpa using hfrontierLenInv.1
                                                          simpa [hfrontierLenVal] using
                                                            hfrontierLength
              · have hcountWord : countWord.val ≠ expectedCount.val := by
                  simpa [actualCount] using hcount
                simp [aspis_core.state_only_private_openings.parse_private_opening_from_proof,
                  hrecord, lift, core.option.Option.ok_or,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  aspis_core.state_only_private_openings.Cursor.new, cursor0, hu16,
                  actualCount, hcount, hcountWord] at hparse

theorem take_four_slices
    {alpha : Type*} (values : List alpha) (a b c d : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    values.take d =
      List.slice 0 a values ++ List.slice a b values ++
        List.slice b c values ++ List.slice c d values := by
  have hab' : a + (b - a) = b := by omega
  have hbc' : b + (c - b) = c := by omega
  have hcd' : c + (d - c) = d := by omega
  calc
    values.take d = values.take c ++
        (values.drop c).take (d - c) := by
          nth_rewrite 1 [← hcd']
          exact List.take_add
    _ = (values.take b ++ (values.drop b).take (c - b)) ++
        (values.drop c).take (d - c) := by
          rw [← hbc', List.take_add, Nat.add_sub_cancel_left]
    _ = ((values.take a ++ (values.drop a).take (b - a)) ++
          (values.drop b).take (c - b)) ++
        (values.drop c).take (d - c) := by
          rw [← hab', List.take_add, Nat.add_sub_cancel_left]
    _ = List.slice 0 a values ++ List.slice a b values ++
        List.slice b c values ++ List.slice c d values := by
          simp [List.slice, List.append_assoc]

theorem successful_parser_consumed_prefix_exact
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (hparse : aspis_core.state_only_private_openings.parse_private_opening_from_proof
      proofBytes expectedCount valueWidth = .ok (.Ok (opening, remainder))) :
    ∃ frontierCount : Nat,
      (proofBytes.val.take opening.offsets.end.val).map generatedU8ToByte =
        u16LE expectedCount.val ++
          opening.records.val.map generatedU8ToByte ++
          u32LE frontierCount ++
          opening.frontier.val.map generatedU8ToByte := by
  have hraw := parse_private_opening_success_exact proofBytes expectedCount
    valueWidth opening remainder hparse
  have hheaders := parse_private_opening_success_headers proofBytes
    expectedCount valueWidth opening remainder hparse
  rcases hraw with ⟨frontierCount, hcount, hwidth, hcountOffset,
    hrecordsOffset, hrecords, hrecordsLength, hfrontierCountOffset,
    hfrontierOffset, hfrontier, hfrontierLength, hend, hendBound,
    hremainder⟩
  rcases hheaders with ⟨headerFrontierCount, hcountHeader,
    hfrontierHeader, hheaderFrontierLength⟩
  have hfrontierCount : headerFrontierCount = frontierCount := by
    omega
  let recordsEnd := 2 + expectedCount.val * (valueWidth.val + 32)
  let frontierStart := recordsEnd + 4
  let sectionEnd := frontierStart + frontierCount * 32
  have hsplit := take_four_slices proofBytes.val 2 recordsEnd
    frontierStart sectionEnd (by simp [recordsEnd])
    (by simp [frontierStart]) (by simp [sectionEnd])
  refine ⟨frontierCount, ?_⟩
  rw [hend]
  change (proofBytes.val.take sectionEnd).map generatedU8ToByte = _
  rw [hsplit]
  simp only [List.map_append]
  have hrecords' :
      (List.slice 2 recordsEnd proofBytes.val).map generatedU8ToByte =
        opening.records.val.map generatedU8ToByte := by
    rw [hrecords]
  have hfrontier' :
      (List.slice frontierStart sectionEnd proofBytes.val).map
          generatedU8ToByte =
        opening.frontier.val.map generatedU8ToByte := by
    rw [hfrontier]
  have hcountHeader' :
      (List.slice 0 2 proofBytes.val).map generatedU8ToByte =
        u16LE expectedCount.val := hcountHeader
  have hfrontierHeader' :
      (List.slice recordsEnd frontierStart proofBytes.val).map
          generatedU8ToByte = u32LE frontierCount := by
    simpa [recordsEnd, frontierStart, hfrontierCount] using
      hfrontierHeader
  rw [hcountHeader', hrecords', hfrontierHeader', hfrontier']

#print axioms u16_from_le_bytes_exact
#print axioms u32_from_le_bytes_exact
#print axioms cursor_u16_success_bytes_exact
#print axioms cursor_u32_success_bytes_exact
#print axioms parse_private_opening_success_headers
#print axioms successful_parser_consumed_prefix_exact

end AspisV5MerkleUnchangedFullWireCanonicality
