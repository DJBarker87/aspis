import V5RelationLinkedTensorFold

namespace AspisV5RelationLinkedGroupedFold

open Aeneas Aeneas.Std Result ControlFlow

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31

def releasedMasks : alloc.vec.Vec Std.U16 :=
  ⟨[0xe7ff#u16, 0xe7fe#u16, 0xeffe#u16, 0x0000#u16,
    0xfff0#u16, 0xfffa#u16, 0xffff#u16], by scalar_tac⟩

private theorem usize_zero_succ :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (1#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_one_succ :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_two_succ :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_three_succ :
    Std.Usize.wrapping_add 3#usize 1#usize = 4#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_four_succ :
    Std.Usize.wrapping_add 4#usize 1#usize = 5#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (5#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_five_succ :
    Std.Usize.wrapping_add 5#usize 1#usize = 6#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (6#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_six_succ :
    Std.Usize.wrapping_add 6#usize 1#usize = 7#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (7#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_seven_succ :
    Std.Usize.wrapping_add 7#usize 1#usize = 8#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (8#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_eight_succ :
    Std.Usize.wrapping_add 8#usize 1#usize = 9#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (9#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_nine_succ :
    Std.Usize.wrapping_add 9#usize 1#usize = 10#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (10#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_ten_succ :
    Std.Usize.wrapping_add 10#usize 1#usize = 11#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (11#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_eleven_succ :
    Std.Usize.wrapping_add 11#usize 1#usize = 12#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (12#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_twelve_succ :
    Std.Usize.wrapping_add 12#usize 1#usize = 13#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (13#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_thirteen_succ :
    Std.Usize.wrapping_add 13#usize 1#usize = 14#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (14#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_fourteen_succ :
    Std.Usize.wrapping_add 14#usize 1#usize = 15#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (15#usize).hSize; scalar_tac)]
  norm_num

private theorem usize_fifteen_succ :
    Std.Usize.wrapping_add 15#usize 1#usize = 16#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (16#usize).hSize; scalar_tac)]
  norm_num

private theorem releasedScanStep0 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body
        (alloc.vec.Vec.deref releasedMasks) 0#u16 false 0#usize =
      ok (cont (0x1800#u16, true, 1#usize)) := by
  have hcountRun : core.num.U16.count_ones 0xe7ff#u16 = ok 14#u32 := by
    rfl
  have hnot : ~~~(0xe7ff#u16) = 0x1800#u16 := by decide
  have hor : 0#u16 ||| 0x1800#u16 = 0x1800#u16 := by decide
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, Slice.index_usize,
    UScalar.lt_equiv, lift, hcountRun, hnot, hor, usize_zero_succ]

private theorem releasedScanStep1 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body
        (alloc.vec.Vec.deref releasedMasks) 0x1800#u16 true 1#usize =
      ok (cont (0x1801#u16, true, 2#usize)) := by
  have hcountRun : core.num.U16.count_ones 0xe7fe#u16 = ok 13#u32 := by rfl
  have hnot : ~~~(0xe7fe#u16) = 0x1801#u16 := by decide
  have hor : 0x1800#u16 ||| 0x1801#u16 = 0x1801#u16 := by decide
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, Slice.index_usize,
    UScalar.lt_equiv, lift, hcountRun, hnot, hor, usize_one_succ]

private theorem releasedScanStep2 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body
        (alloc.vec.Vec.deref releasedMasks) 0x1801#u16 true 2#usize =
      ok (cont (0x1801#u16, true, 3#usize)) := by
  have hcountRun : core.num.U16.count_ones 0xeffe#u16 = ok 14#u32 := by rfl
  have hnot : ~~~(0xeffe#u16) = 0x1001#u16 := by decide
  have hor : 0x1801#u16 ||| 0x1001#u16 = 0x1801#u16 := by decide
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, Slice.index_usize,
    UScalar.lt_equiv, lift, hcountRun, hnot, hor, usize_two_succ]

private theorem releasedScanStep3 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body
        (alloc.vec.Vec.deref releasedMasks) 0x1801#u16 true 3#usize =
      ok (cont (0x1801#u16, true, 4#usize)) := by
  have hcountRun : core.num.U16.count_ones 0x0000#u16 = ok 0#u32 := by rfl
  have hor : 0x1801#u16 ||| 0x0000#u16 = 0x1801#u16 := by decide
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, Slice.index_usize,
    UScalar.lt_equiv, lift, hcountRun, hor, usize_three_succ]

private theorem releasedScanStep4 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body
        (alloc.vec.Vec.deref releasedMasks) 0x1801#u16 true 4#usize =
      ok (cont (0x180f#u16, true, 5#usize)) := by
  have hcountRun : core.num.U16.count_ones 0xfff0#u16 = ok 12#u32 := by rfl
  have hnot : ~~~(0xfff0#u16) = 0x000f#u16 := by decide
  have hor : 0x1801#u16 ||| 0x000f#u16 = 0x180f#u16 := by decide
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, Slice.index_usize,
    UScalar.lt_equiv, lift, hcountRun, hnot, hor, usize_four_succ]

private theorem releasedScanStep5 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body
        (alloc.vec.Vec.deref releasedMasks) 0x180f#u16 true 5#usize =
      ok (cont (0x180f#u16, true, 6#usize)) := by
  have hcountRun : core.num.U16.count_ones 0xfffa#u16 = ok 14#u32 := by rfl
  have hnot : ~~~(0xfffa#u16) = 0x0005#u16 := by decide
  have hor : 0x180f#u16 ||| 0x0005#u16 = 0x180f#u16 := by decide
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, Slice.index_usize,
    UScalar.lt_equiv, lift, hcountRun, hnot, hor, usize_five_succ]

private theorem releasedScanStep6 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body
        (alloc.vec.Vec.deref releasedMasks) 0x180f#u16 true 6#usize =
      ok (cont (0x180f#u16, true, 7#usize)) := by
  have hcountRun : core.num.U16.count_ones 0xffff#u16 = ok 16#u32 := by rfl
  have hnot : ~~~(0xffff#u16) = 0x0000#u16 := by decide
  have hor : 0x180f#u16 ||| 0x0000#u16 = 0x180f#u16 := by decide
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, Slice.index_usize,
    UScalar.lt_equiv, lift, hcountRun, hnot, hor, usize_six_succ]

private theorem releasedScanDone :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body
        (alloc.vec.Vec.deref releasedMasks) 0x180f#u16 true 7#usize =
      ok (done (0x180f#u16, true)) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, UScalar.lt_equiv]

theorem releasedMaskScanExact :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0
        (alloc.vec.Vec.deref releasedMasks) 0#u16 false 0#usize =
      ok (0x180f#u16, true) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop0
  rw [loop.eq_1]
  dsimp only
  rw [releasedScanStep0]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [releasedScanStep1]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [releasedScanStep2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [releasedScanStep3]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [releasedScanStep4]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [releasedScanStep5]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [releasedScanStep6]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [releasedScanDone]

def releasedBasis
    (alpha0Cubed alpha0Squared alpha0 alpha1SquaredTimesAlpha0 alpha1 : RawQM31) :
    Array RawQM31 16#usize :=
  Array.make 16#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    alpha0Cubed, alpha0Squared, alpha0,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    alpha1SquaredTimesAlpha0,
    alpha1,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private theorem arrayUpdateExact {N : Std.Usize}
    (values : Array RawQM31 N) (index : Std.Usize)
    (hindex : index.val < N.val) (value : RawQM31) :
    Array.update values index value = ok (values.set index value) := by
  unfold Array.update
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem (by rw [values.property]; exact hindex)]
  apply congrArg Result.ok
  apply Subtype.ext
  rfl

private theorem releasedBasisUnselectedStep
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) (low next : Std.Usize)
    (bit : Std.U16)
    (hactive : low < 16#usize)
    (hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount low) = bit)
    (hoff : 0x180f#u16 &&& bit = 0#u16)
    (hnext : Std.Usize.wrapping_add low 1#usize = next) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis low =
      ok (cont (basis, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
  rw [if_pos hactive, hshift]
  simp only [lift, bind_tc_ok]
  rw [hoff]
  rw [if_neg (by decide)]
  rw [hnext]

private theorem releasedBasisHighZeroStep
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis basisOut : Array RawQM31 16#usize)
    (low next lowSlot : Std.Usize) (bit : Std.U16) (q : RawQM31)
    (hactive : low < 16#usize)
    (hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount low) = bit)
    (hon : 0x180f#u16 &&& bit = bit)
    (hbit : bit != 0#u16)
    (hhigh : Std.Usize.wrapping_shr low 2#u32 = 0#usize)
    (hlow : low &&& 3#usize = lowSlot)
    (hindex : Array.index_usize alpha0Powers lowSlot = ok q)
    (hupdate : Array.update basis low q = ok basisOut)
    (hnext : Std.Usize.wrapping_add low 1#usize = next) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis low =
      ok (cont (basisOut, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
  rw [if_pos hactive, hshift]
  simp only [lift, bind_tc_ok]
  rw [hon]
  rw [if_pos hbit]
  rw [hhigh, hlow]
  rw [if_pos rfl]
  rw [hindex]
  simp only [bind_tc_ok]
  rw [hupdate]
  simp only [bind_tc_ok, hnext]

private theorem releasedBasisCrossStep
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis basisOut : Array RawQM31 16#usize)
    (low next highSlot lowSlot : Std.Usize) (bit : Std.U16)
    (left right product : RawQM31)
    (hactive : low < 16#usize)
    (hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount low) = bit)
    (hon : 0x180f#u16 &&& bit = bit)
    (hbit : bit != 0#u16)
    (hhigh : Std.Usize.wrapping_shr low 2#u32 = highSlot)
    (hhighNonzero : highSlot ≠ 0#usize)
    (hlow : low &&& 3#usize = lowSlot)
    (hlowNonzero : lowSlot ≠ 0#usize)
    (hleft : Array.index_usize alpha1Powers highSlot = ok left)
    (hright : Array.index_usize alpha0Powers lowSlot = ok right)
    (hmul : V5RelationLinkedGenerated.aspis_core.field.QM31.mul left right =
      ok product)
    (hupdate : Array.update basis low product = ok basisOut)
    (hnext : Std.Usize.wrapping_add low 1#usize = next) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis low =
      ok (cont (basisOut, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
  rw [if_pos hactive, hshift]
  simp only [lift, bind_tc_ok]
  rw [hon]
  rw [if_pos hbit]
  rw [hhigh, hlow]
  rw [if_neg hhighNonzero, if_neg hlowNonzero]
  rw [hleft]
  simp only [bind_tc_ok]
  rw [hright]
  simp only [bind_tc_ok]
  rw [hmul]
  simp only [bind_tc_ok]
  rw [hupdate]
  simp only [bind_tc_ok, hnext]

private theorem releasedBasisLowZeroStep
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis basisOut : Array RawQM31 16#usize)
    (low next highSlot : Std.Usize) (bit : Std.U16) (q : RawQM31)
    (hactive : low < 16#usize)
    (hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount low) = bit)
    (hon : 0x180f#u16 &&& bit = bit)
    (hbit : bit != 0#u16)
    (hhigh : Std.Usize.wrapping_shr low 2#u32 = highSlot)
    (hhighNonzero : highSlot ≠ 0#usize)
    (hlow : low &&& 3#usize = 0#usize)
    (hindex : Array.index_usize alpha1Powers highSlot = ok q)
    (hupdate : Array.update basis low q = ok basisOut)
    (hnext : Std.Usize.wrapping_add low 1#usize = next) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis low =
      ok (cont (basisOut, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
  rw [if_pos hactive, hshift]
  simp only [lift, bind_tc_ok]
  rw [hon]
  rw [if_pos hbit]
  rw [hhigh, hlow]
  rw [if_neg hhighNonzero, if_pos rfl]
  rw [hindex]
  simp only [bind_tc_ok]
  rw [hupdate]
  simp only [bind_tc_ok, hnext]

private theorem usizeShiftCountSmall (low : Std.Usize)
    (hsmall : low.val < 16) :
    (V5RelationLinkedGenerated.usizeShiftCount low).val = low.val := by
  unfold V5RelationLinkedGenerated.usizeShiftCount
  change (low.bv.setWidth 32).toNat = low.val
  rw [BitVec.toNat_setWidth, Std.Usize.bv_toNat]
  apply Nat.mod_eq_of_lt
  omega

private theorem usizeShiftCountOne :
    V5RelationLinkedGenerated.usizeShiftCount 1#usize = 1#u32 := by
  apply UScalar.val_eq_imp
  rw [usizeShiftCountSmall 1#usize (by decide)]
  rfl

private theorem usizeShiftCountEq (low : Std.Usize) (shift : Std.U32)
    (hsmall : low.val < 16) (hval : low.val = shift.val) :
    V5RelationLinkedGenerated.usizeShiftCount low = shift := by
  apply UScalar.val_eq_imp
  rw [usizeShiftCountSmall low hsmall]
  exact hval

private theorem usizeShrTwoVal (low : Std.Usize) :
    (Std.Usize.wrapping_shr low 2#u32).val = low.val >>> 2 := by
  change (Std.Usize.wrapping_shr low 2#u32).bv.toNat =
    low.bv.toNat >>> 2
  rw [Std.Usize.wrapping_shr_bv_eq]
  have hshift : (2#u32).val % System.Platform.numBits = 2 := by
    cases System.Platform.numBits_eq <;> simp_all
  rw [hshift]
  change (low.bv >>> (2 : Nat)).toNat = low.bv.toNat >>> 2
  rw [BitVec.toNat_ushiftRight]

private theorem oneShiftVia
    (low : Std.Usize) (shift : Std.U32) (bit : Std.U16)
    (hcount : V5RelationLinkedGenerated.usizeShiftCount low = shift)
    (hshift : Std.U16.wrapping_shl 1#u16 shift = bit) :
    Std.U16.wrapping_shl 1#u16
        (V5RelationLinkedGenerated.usizeShiftCount low) = bit := by
  rw [hcount]
  exact hshift

def releasedBasis0 : Array RawQM31 16#usize :=
  Array.repeat 16#usize V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO

def releasedBasis1 : Array RawQM31 16#usize :=
  releasedBasis0.set 0#usize V5RelationLinkedGenerated.aspis_core.field.QM31.ONE

def releasedAlpha0Powers
    (alpha0 alpha0Squared alpha0Cubed : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    alpha0Cubed, alpha0Squared, alpha0]

def releasedAlpha1Powers
    (alpha1 alpha1Squared alpha1Cubed : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    alpha1Cubed, alpha1Squared, alpha1]

def releasedBasis2 (alpha0Cubed : RawQM31) : Array RawQM31 16#usize :=
  releasedBasis1.set 1#usize alpha0Cubed

def releasedBasis3 (alpha0Cubed alpha0Squared : RawQM31) :
    Array RawQM31 16#usize :=
  (releasedBasis2 alpha0Cubed).set 2#usize alpha0Squared

def releasedBasis4 (alpha0Cubed alpha0Squared alpha0 : RawQM31) :
    Array RawQM31 16#usize :=
  (releasedBasis3 alpha0Cubed alpha0Squared).set 3#usize alpha0

def releasedBasis12
    (alpha0Cubed alpha0Squared alpha0 alpha1SquaredTimesAlpha0 : RawQM31) :
    Array RawQM31 16#usize :=
  (releasedBasis4 alpha0Cubed alpha0Squared alpha0).set 11#usize
    alpha1SquaredTimesAlpha0

def releasedBasis13
    (alpha0Cubed alpha0Squared alpha0 alpha1SquaredTimesAlpha0 alpha1 :
      RawQM31) : Array RawQM31 16#usize :=
  (releasedBasis12 alpha0Cubed alpha0Squared alpha0
    alpha1SquaredTimesAlpha0).set 12#usize alpha1

private theorem releasedBasisStep0
    (alpha0 alpha0Squared alpha0Cubed alpha1 alpha1Squared alpha1Cubed :
      RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        (Array.make 4#usize [
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
          alpha0Cubed, alpha0Squared, alpha0])
        (Array.make 4#usize [
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
          alpha1Cubed, alpha1Squared, alpha1])
        0x180f#u16 releasedBasis0 0#usize =
      ok (cont (releasedBasis1, 1#usize)) := by
  have hupdate := arrayUpdateExact releasedBasis0 0#usize (by decide)
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
  have hshiftCount :
      V5RelationLinkedGenerated.usizeShiftCount 0#usize = 0#u32 := by
    cases System.Platform.numBits_eq <;>
      simp_all [V5RelationLinkedGenerated.usizeShiftCount]
    all_goals
      apply Std.U32.bv_eq_imp_eq
      rfl
  have hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount 0#usize) = 1#u16 := by
    rw [hshiftCount]
    apply Std.U16.bv_eq_imp_eq
    simp
  have hselected : 0x180f#u16 &&& 1#u16 = 1#u16 := by decide
  have hhigh : Std.Usize.wrapping_shr 0#usize 2#u32 = 0#usize := by
    apply Std.Usize.bv_eq_imp_eq
    simp [Std.Usize.wrapping_shr, UScalar.wrapping_shr]
  have hlow : 0#usize &&& 3#usize = 0#usize := by decide
  have hindex :
      Array.index_usize
        (Array.make 4#usize [
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
          alpha0Cubed, alpha0Squared, alpha0]) 0#usize =
        ok V5RelationLinkedGenerated.aspis_core.field.QM31.ONE := by
    rfl
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
  rw [if_pos (by decide)]
  rw [hshift]
  simp only [lift, bind_tc_ok]
  rw [hselected]
  rw [if_pos (by decide)]
  rw [hhigh, hlow]
  rw [if_pos rfl]
  rw [hindex]
  simp only [bind_tc_ok]
  rw [hupdate]
  simp only [bind_tc_ok, usize_zero_succ]
  rfl

private theorem releasedBasisStep1
    (alpha0 alpha0Squared alpha0Cubed alpha1 alpha1Squared alpha1Cubed :
      RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
        (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
        0x180f#u16 releasedBasis1 1#usize =
      ok (cont (releasedBasis2 alpha0Cubed, 2#usize)) := by
  have hcount : V5RelationLinkedGenerated.usizeShiftCount 1#usize = 1#u32 :=
    usizeShiftCountEq 1#usize 1#u32 (by decide) rfl
  have hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount 1#usize) = 2#u16 := by
    rw [hcount]
    apply Std.U16.bv_eq_imp_eq
    decide
  have hhigh : Std.Usize.wrapping_shr 1#usize 2#u32 = 0#usize := by
    apply UScalar.val_eq_imp
    unfold Std.Usize.wrapping_shr UScalar.wrapping_shr UScalar.val
    cases System.Platform.numBits_eq <;>
      simp_all [BitVec.toNat_ushiftRight]
  have hupdate : Array.update releasedBasis1 1#usize alpha0Cubed =
      ok (releasedBasis2 alpha0Cubed) := by
    simpa [releasedBasis2] using
      arrayUpdateExact releasedBasis1 1#usize (by decide) alpha0Cubed
  apply releasedBasisHighZeroStep
    (alpha0Powers := releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (alpha1Powers := releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (basis := releasedBasis1) (basisOut := releasedBasis2 alpha0Cubed)
    (low := 1#usize) (next := 2#usize) (lowSlot := 1#usize)
    (bit := 2#u16) (q := alpha0Cubed)
    (by decide) hshift (by decide) (by decide) hhigh (by decide)
    (by rfl) hupdate usize_one_succ

private theorem releasedBasisStep2
    (alpha0 alpha0Squared alpha0Cubed alpha1 alpha1Squared alpha1Cubed :
      RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
        (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
        0x180f#u16 (releasedBasis2 alpha0Cubed) 2#usize =
      ok (cont (releasedBasis3 alpha0Cubed alpha0Squared, 3#usize)) := by
  have hcount : V5RelationLinkedGenerated.usizeShiftCount 2#usize = 2#u32 :=
    usizeShiftCountEq 2#usize 2#u32 (by decide) rfl
  have hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount 2#usize) = 4#u16 := by
    rw [hcount]
    apply Std.U16.bv_eq_imp_eq
    decide
  have hhigh : Std.Usize.wrapping_shr 2#usize 2#u32 = 0#usize := by
    apply UScalar.val_eq_imp
    rw [usizeShrTwoVal]
    rfl
  have hupdate : Array.update (releasedBasis2 alpha0Cubed) 2#usize
      alpha0Squared = ok (releasedBasis3 alpha0Cubed alpha0Squared) := by
    simpa [releasedBasis3] using
      arrayUpdateExact (releasedBasis2 alpha0Cubed) 2#usize (by decide)
        alpha0Squared
  apply releasedBasisHighZeroStep
    (alpha0Powers := releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (alpha1Powers := releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (basis := releasedBasis2 alpha0Cubed)
    (basisOut := releasedBasis3 alpha0Cubed alpha0Squared)
    (low := 2#usize) (next := 3#usize) (lowSlot := 2#usize)
    (bit := 4#u16) (q := alpha0Squared)
    (by decide) hshift (by decide) (by decide) hhigh (by decide)
    (by rfl) hupdate usize_two_succ

private theorem releasedBasisStep3
    (alpha0 alpha0Squared alpha0Cubed alpha1 alpha1Squared alpha1Cubed :
      RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
        (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
        0x180f#u16 (releasedBasis3 alpha0Cubed alpha0Squared) 3#usize =
      ok (cont (releasedBasis4 alpha0Cubed alpha0Squared alpha0, 4#usize)) := by
  have hcount : V5RelationLinkedGenerated.usizeShiftCount 3#usize = 3#u32 :=
    usizeShiftCountEq 3#usize 3#u32 (by decide) rfl
  have hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount 3#usize) = 8#u16 := by
    rw [hcount]
    apply Std.U16.bv_eq_imp_eq
    decide
  have hhigh : Std.Usize.wrapping_shr 3#usize 2#u32 = 0#usize := by
    apply UScalar.val_eq_imp
    rw [usizeShrTwoVal]
    rfl
  have hupdate : Array.update (releasedBasis3 alpha0Cubed alpha0Squared)
      3#usize alpha0 = ok (releasedBasis4 alpha0Cubed alpha0Squared alpha0) := by
    simpa [releasedBasis4] using
      arrayUpdateExact (releasedBasis3 alpha0Cubed alpha0Squared) 3#usize
        (by decide) alpha0
  apply releasedBasisHighZeroStep
    (alpha0Powers := releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (alpha1Powers := releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (basis := releasedBasis3 alpha0Cubed alpha0Squared)
    (basisOut := releasedBasis4 alpha0Cubed alpha0Squared alpha0)
    (low := 3#usize) (next := 4#usize) (lowSlot := 3#usize)
    (bit := 8#u16) (q := alpha0)
    (by decide) hshift (by decide) (by decide) hhigh (by decide)
    (by rfl) hupdate usize_three_succ

private theorem releasedBasisStep4
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 4#usize =
      ok (cont (basis, 5#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 4#usize) (next := 5#usize) (bit := 0x0010#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 4#usize 4#u32 0x0010#u16
      (usizeShiftCountEq 4#usize 4#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_four_succ)

private theorem releasedBasisStep5
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 5#usize =
      ok (cont (basis, 6#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 5#usize) (next := 6#usize) (bit := 0x0020#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 5#usize 5#u32 0x0020#u16
      (usizeShiftCountEq 5#usize 5#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_five_succ)

private theorem releasedBasisStep6
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 6#usize =
      ok (cont (basis, 7#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 6#usize) (next := 7#usize) (bit := 0x0040#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 6#usize 6#u32 0x0040#u16
      (usizeShiftCountEq 6#usize 6#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_six_succ)

private theorem releasedBasisStep7
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 7#usize =
      ok (cont (basis, 8#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 7#usize) (next := 8#usize) (bit := 0x0080#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 7#usize 7#u32 0x0080#u16
      (usizeShiftCountEq 7#usize 7#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_seven_succ)

private theorem releasedBasisStep8
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 8#usize =
      ok (cont (basis, 9#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 8#usize) (next := 9#usize) (bit := 0x0100#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 8#usize 8#u32 0x0100#u16
      (usizeShiftCountEq 8#usize 8#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_eight_succ)

private theorem releasedBasisStep9
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 9#usize =
      ok (cont (basis, 10#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 9#usize) (next := 10#usize) (bit := 0x0200#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 9#usize 9#u32 0x0200#u16
      (usizeShiftCountEq 9#usize 9#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_nine_succ)

private theorem releasedBasisStep10
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 10#usize =
      ok (cont (basis, 11#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 10#usize) (next := 11#usize) (bit := 0x0400#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 10#usize 10#u32 0x0400#u16
      (usizeShiftCountEq 10#usize 10#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_ten_succ)

private theorem releasedBasisStep11
    (alpha0 alpha0Squared alpha0Cubed alpha1 alpha1Squared alpha1Cubed
      alpha1SquaredTimesAlpha0 : RawQM31)
    (crossRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha1Squared alpha0 =
        ok alpha1SquaredTimesAlpha0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
        (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
        0x180f#u16 (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
          11#usize =
      ok (cont (releasedBasis12 alpha0Cubed alpha0Squared alpha0
        alpha1SquaredTimesAlpha0, 12#usize)) := by
  have hshift := oneShiftVia 11#usize 11#u32 0x0800#u16
    (usizeShiftCountEq 11#usize 11#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)
  have hhigh : Std.Usize.wrapping_shr 11#usize 2#u32 = 2#usize := by
    apply UScalar.val_eq_imp
    rw [usizeShrTwoVal]
    rfl
  have hupdate :
      Array.update (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
        11#usize alpha1SquaredTimesAlpha0 =
      ok (releasedBasis12 alpha0Cubed alpha0Squared alpha0
        alpha1SquaredTimesAlpha0) := by
    simpa [releasedBasis12] using
      arrayUpdateExact (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
        11#usize (by decide) alpha1SquaredTimesAlpha0
  apply releasedBasisCrossStep
    (alpha0Powers := releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (alpha1Powers := releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (basis := releasedBasis4 alpha0Cubed alpha0Squared alpha0)
    (basisOut := releasedBasis12 alpha0Cubed alpha0Squared alpha0
      alpha1SquaredTimesAlpha0)
    (low := 11#usize) (next := 12#usize) (highSlot := 2#usize)
    (lowSlot := 3#usize) (bit := 0x0800#u16)
    (left := alpha1Squared) (right := alpha0)
    (product := alpha1SquaredTimesAlpha0)
    (hactive := by decide) (hshift := hshift) (hon := by decide)
    (hbit := by decide) (hhigh := hhigh) (hhighNonzero := by decide)
    (hlow := by decide) (hlowNonzero := by decide)
    (hleft := by rfl) (hright := by rfl) (hmul := crossRun)
    (hupdate := hupdate) (hnext := usize_eleven_succ)

private theorem releasedBasisStep12
    (alpha0 alpha0Squared alpha0Cubed alpha1 alpha1Squared alpha1Cubed
      alpha1SquaredTimesAlpha0 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
        (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
        0x180f#u16 (releasedBasis12 alpha0Cubed alpha0Squared alpha0
          alpha1SquaredTimesAlpha0) 12#usize =
      ok (cont (releasedBasis13 alpha0Cubed alpha0Squared alpha0
        alpha1SquaredTimesAlpha0 alpha1, 13#usize)) := by
  have hshift := oneShiftVia 12#usize 12#u32 0x1000#u16
    (usizeShiftCountEq 12#usize 12#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)
  have hhigh : Std.Usize.wrapping_shr 12#usize 2#u32 = 3#usize := by
    apply UScalar.val_eq_imp
    rw [usizeShrTwoVal]
    rfl
  have hupdate :
      Array.update (releasedBasis12 alpha0Cubed alpha0Squared alpha0
        alpha1SquaredTimesAlpha0) 12#usize alpha1 =
      ok (releasedBasis13 alpha0Cubed alpha0Squared alpha0
        alpha1SquaredTimesAlpha0 alpha1) := by
    simpa [releasedBasis13] using
      arrayUpdateExact (releasedBasis12 alpha0Cubed alpha0Squared alpha0
        alpha1SquaredTimesAlpha0) 12#usize (by decide) alpha1
  apply releasedBasisLowZeroStep
    (alpha0Powers := releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (alpha1Powers := releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (basis := releasedBasis12 alpha0Cubed alpha0Squared alpha0
      alpha1SquaredTimesAlpha0)
    (basisOut := releasedBasis13 alpha0Cubed alpha0Squared alpha0
      alpha1SquaredTimesAlpha0 alpha1)
    (low := 12#usize) (next := 13#usize) (highSlot := 3#usize)
    (bit := 0x1000#u16) (q := alpha1)
    (hactive := by decide) (hshift := hshift) (hon := by decide)
    (hbit := by decide) (hhigh := hhigh) (hhighNonzero := by decide)
    (hlow := by decide) (hindex := by rfl) (hupdate := hupdate)
    (hnext := usize_twelve_succ)

private theorem releasedBasisStep13
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 13#usize =
      ok (cont (basis, 14#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 13#usize) (next := 14#usize) (bit := 0x2000#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 13#usize 13#u32 0x2000#u16
      (usizeShiftCountEq 13#usize 13#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_thirteen_succ)

private theorem releasedBasisStep14
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 14#usize =
      ok (cont (basis, 15#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 14#usize) (next := 15#usize) (bit := 0x4000#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 14#usize 14#u32 0x4000#u16
      (usizeShiftCountEq 14#usize 14#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_fourteen_succ)

private theorem releasedBasisStep15
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 15#usize =
      ok (cont (basis, 16#usize)) := by
  apply releasedBasisUnselectedStep
    (low := 15#usize) (next := 16#usize) (bit := 0x8000#u16)
    (hactive := by decide)
    (hshift := oneShiftVia 15#usize 15#u32 0x8000#u16
      (usizeShiftCountEq 15#usize 15#u32 (by decide) rfl)
      (by apply Std.U16.bv_eq_imp_eq; decide))
    (hoff := by decide) (hnext := usize_fifteen_succ)

private theorem releasedBasisDone
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
        alpha0Powers alpha1Powers 0x180f#u16 basis 16#usize =
      ok (done basis) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
  rw [if_neg (by decide)]

private theorem releasedBasis13_eq_releasedBasis
    (alpha0Cubed alpha0Squared alpha0 alpha1SquaredTimesAlpha0 alpha1 :
      RawQM31) :
    releasedBasis13 alpha0Cubed alpha0Squared alpha0
        alpha1SquaredTimesAlpha0 alpha1 =
      releasedBasis alpha0Cubed alpha0Squared alpha0
        alpha1SquaredTimesAlpha0 alpha1 := by
  apply Subtype.ext
  simp [releasedBasis13, releasedBasis12, releasedBasis4, releasedBasis3,
    releasedBasis2, releasedBasis1, releasedBasis0, releasedBasis,
    Array.set_val_eq, Array.make]

theorem releasedBasisLoopExact
    (alpha0 alpha0Squared alpha0Cubed alpha1 alpha1Squared alpha1Cubed
      alpha1SquaredTimesAlpha0 : RawQM31)
    (crossRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha1Squared alpha0 =
        ok alpha1SquaredTimesAlpha0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1
        (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
        (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
        0x180f#u16 releasedBasis0 0#usize =
      ok (releasedBasis alpha0Cubed alpha0Squared alpha0
        alpha1SquaredTimesAlpha0 alpha1) := by
  have step0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1.body
          (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
          (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
          0x180f#u16 releasedBasis0 0#usize =
        ok (cont (releasedBasis1, 1#usize)) := by
    simpa [releasedAlpha0Powers, releasedAlpha1Powers] using
      releasedBasisStep0 alpha0 alpha0Squared alpha0Cubed alpha1
        alpha1Squared alpha1Cubed
  have step1 := releasedBasisStep1 alpha0 alpha0Squared alpha0Cubed alpha1
    alpha1Squared alpha1Cubed
  have step2 := releasedBasisStep2 alpha0 alpha0Squared alpha0Cubed alpha1
    alpha1Squared alpha1Cubed
  have step3 := releasedBasisStep3 alpha0 alpha0Squared alpha0Cubed alpha1
    alpha1Squared alpha1Cubed
  have step4 := releasedBasisStep4
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
  have step5 := releasedBasisStep5
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
  have step6 := releasedBasisStep6
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
  have step7 := releasedBasisStep7
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
  have step8 := releasedBasisStep8
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
  have step9 := releasedBasisStep9
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
  have step10 := releasedBasisStep10
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    (releasedBasis4 alpha0Cubed alpha0Squared alpha0)
  have step11 := releasedBasisStep11 alpha0 alpha0Squared alpha0Cubed alpha1
    alpha1Squared alpha1Cubed alpha1SquaredTimesAlpha0 crossRun
  have step12 := releasedBasisStep12 alpha0 alpha0Squared alpha0Cubed alpha1
    alpha1Squared alpha1Cubed alpha1SquaredTimesAlpha0
  let basis13 := releasedBasis13 alpha0Cubed alpha0Squared alpha0
    alpha1SquaredTimesAlpha0 alpha1
  have step13 := releasedBasisStep13
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed) basis13
  have step14 := releasedBasisStep14
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed) basis13
  have step15 := releasedBasisStep15
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed) basis13
  have done := releasedBasisDone
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed) basis13
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop1
  rw [loop.eq_1]
  dsimp only
  rw [step0]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step1]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step2]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step3]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step4]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step5]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step6]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step7]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step8]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step9]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step10]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step11]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step12]
  simp only
  rw [loop.eq_1]
  dsimp only [basis13]
  rw [step13]
  simp only
  rw [loop.eq_1]
  dsimp only [basis13]
  rw [step14]
  simp only
  rw [loop.eq_1]
  dsimp only [basis13]
  rw [step15]
  simp only
  rw [loop.eq_1]
  dsimp only [basis13]
  rw [done]
  simp only
  dsimp only [basis13]
  rw [releasedBasis13_eq_releasedBasis alpha0Cubed alpha0Squared alpha0
    alpha1SquaredTimesAlpha0 alpha1]

end AspisV5RelationLinkedGroupedFold
