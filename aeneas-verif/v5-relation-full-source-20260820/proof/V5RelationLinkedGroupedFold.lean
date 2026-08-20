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

private theorem releasedPowerTotalStep
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (alpha0Total alpha1Total alpha0Term alpha1Term
      alpha0TotalOut alpha1TotalOut : RawQM31)
    (slot next : Std.Usize)
    (hactive : slot < 4#usize)
    (hread0 : Array.index_usize alpha0Powers slot = ok alpha0Term)
    (hadd0 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          alpha0Total alpha0Term = ok alpha0TotalOut)
    (hread1 : Array.index_usize alpha1Powers slot = ok alpha1Term)
    (hadd1 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          alpha1Total alpha1Term = ok alpha1TotalOut)
    (hnext : Std.Usize.wrapping_add slot 1#usize = next) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop4.body
        alpha0Powers alpha1Powers alpha0Total alpha1Total slot =
      ok (cont (alpha0TotalOut, alpha1TotalOut, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop4.body
  rw [if_pos hactive, hread0]
  simp only [bind_tc_ok]
  rw [hadd0]
  simp only [bind_tc_ok]
  rw [hread1]
  simp only [bind_tc_ok]
  rw [hadd1]
  simp only [bind_tc_ok, lift, hnext]

private theorem releasedPowerTotalDone
    (alpha0Powers alpha1Powers : Array RawQM31 4#usize)
    (alpha0Total alpha1Total : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop4.body
        alpha0Powers alpha1Powers alpha0Total alpha1Total 4#usize =
      ok (done (alpha0Total, alpha1Total)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop4.body
  rw [if_neg (by decide)]

/-- The extracted fixed-release total loop reads the four powers in their
source order for both challenges.  The theorem deliberately names every
field addition result; the field-semantics theorem can therefore connect this
source trace to ordinary sums without hiding the executed schedule. -/
theorem releasedPowerTotalsLoopExact
    (alpha0 alpha0Squared alpha0Cubed alpha1 alpha1Squared alpha1Cubed :
      RawQM31)
    (alpha0Total0 alpha0Total1 alpha0Total2 alpha0Total3
      alpha1Total0 alpha1Total1 alpha1Total2 alpha1Total3 : RawQM31)
    (hadd00 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE =
        ok alpha0Total0)
    (hadd10 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE =
        ok alpha1Total0)
    (hadd01 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          alpha0Total0 alpha0Cubed = ok alpha0Total1)
    (hadd11 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          alpha1Total0 alpha1Cubed = ok alpha1Total1)
    (hadd02 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          alpha0Total1 alpha0Squared = ok alpha0Total2)
    (hadd12 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          alpha1Total1 alpha1Squared = ok alpha1Total2)
    (hadd03 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          alpha0Total2 alpha0 = ok alpha0Total3)
    (hadd13 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          alpha1Total2 alpha1 = ok alpha1Total3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop4
        (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
        (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO 0#usize =
      ok (alpha0Total3, alpha1Total3) := by
  have step0 := releasedPowerTotalStep
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
    alpha0Total0 alpha1Total0 0#usize 1#usize
    (by decide) (by rfl) hadd00 (by rfl) hadd10 usize_zero_succ
  have step1 := releasedPowerTotalStep
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    alpha0Total0 alpha1Total0 alpha0Cubed alpha1Cubed
    alpha0Total1 alpha1Total1 1#usize 2#usize
    (by decide) (by rfl) hadd01 (by rfl) hadd11 usize_one_succ
  have step2 := releasedPowerTotalStep
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    alpha0Total1 alpha1Total1 alpha0Squared alpha1Squared
    alpha0Total2 alpha1Total2 2#usize 3#usize
    (by decide) (by rfl) hadd02 (by rfl) hadd12 usize_two_succ
  have step3 := releasedPowerTotalStep
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    alpha0Total2 alpha1Total2 alpha0 alpha1
    alpha0Total3 alpha1Total3 3#usize 4#usize
    (by decide) (by rfl) hadd03 (by rfl) hadd13 usize_three_succ
  have done := releasedPowerTotalDone
    (releasedAlpha0Powers alpha0 alpha0Squared alpha0Cubed)
    (releasedAlpha1Powers alpha1 alpha1Squared alpha1Cubed)
    alpha0Total3 alpha1Total3
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop4
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
  rw [done]

structure DenseMaskValueTrace (selected : Std.U16)
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31) where
  partialSum : RawQM31
  raw : RawQM31
  half0 : RawQM31
  half1 : RawQM31
  half2 : RawQM31
  value : RawQM31
  sumRun :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        selected basis = ok partialSum
  subRun :
    V5RelationLinkedGenerated.aspis_core.field.QM31.sub total partialSum =
      ok raw
  half0Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.half raw = ok half0
  half1Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.half half0 = ok half1
  half2Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok half2
  half3Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.half half2 = ok value
  pushRun : alloc.vec.Vec.push values value = ok valuesOut

structure SparseMaskValueTrace (selected : Std.U16)
    (basis : Array RawQM31 16#usize)
    (values valuesOut : alloc.vec.Vec RawQM31) where
  partialSum : RawQM31
  half0 : RawQM31
  half1 : RawQM31
  half2 : RawQM31
  value : RawQM31
  sumRun :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        selected basis = ok partialSum
  half0Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.half partialSum = ok half0
  half1Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.half half0 = ok half1
  half2Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok half2
  half3Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.half half2 = ok value
  pushRun : alloc.vec.Vec.push values value = ok valuesOut

private theorem releasedMaskValueStep0
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (trace : DenseMaskValueTrace 0x1800#u16 basis total values valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values 0#usize =
      ok (cont (valuesOut, 1#usize)) := by
  have hcountRun : core.num.U16.count_ones 0xe7ff#u16 = ok 14#u32 := by
    rfl
  have hnot : ~~~(0xe7ff#u16) = 0x1800#u16 := by decide
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, Slice.index_usize,
    UScalar.lt_equiv, lift, hcountRun, hnot, trace.sumRun, trace.subRun,
    trace.half0Run, trace.half1Run, trace.half2Run, trace.half3Run,
    trace.pushRun, usize_zero_succ]

private theorem releasedDenseMaskValueStep
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (maskIndex next : Std.Usize) (mask selected : Std.U16)
    (count : Std.U32)
    (hactive : maskIndex < Slice.len (alloc.vec.Vec.deref releasedMasks))
    (hread :
      Slice.index_usize (alloc.vec.Vec.deref releasedMasks) maskIndex =
        ok mask)
    (hcount : core.num.U16.count_ones mask = ok count)
    (hdense : count > 8#u32)
    (hcomplement : ~~~mask = selected)
    (hnext : Std.Usize.wrapping_add maskIndex 1#usize = next)
    (trace : DenseMaskValueTrace selected basis total values valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values maskIndex =
      ok (cont (valuesOut, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
  rw [if_pos hactive, hread]
  simp only [bind_tc_ok]
  rw [hcount]
  simp only [bind_tc_ok]
  rw [if_pos hdense]
  simp only [lift, bind_tc_ok]
  rw [hcomplement, trace.sumRun]
  simp only [bind_tc_ok]
  rw [trace.subRun]
  simp only [bind_tc_ok]
  rw [trace.half0Run]
  simp only [bind_tc_ok]
  rw [trace.half1Run]
  simp only [bind_tc_ok]
  rw [trace.half2Run]
  simp only [bind_tc_ok]
  rw [trace.half3Run]
  simp only [bind_tc_ok]
  rw [trace.pushRun]
  simp [hnext]

private theorem releasedSparseMaskValueStep
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (maskIndex next : Std.Usize) (mask : Std.U16) (count : Std.U32)
    (hactive : maskIndex < Slice.len (alloc.vec.Vec.deref releasedMasks))
    (hread :
      Slice.index_usize (alloc.vec.Vec.deref releasedMasks) maskIndex =
        ok mask)
    (hcount : core.num.U16.count_ones mask = ok count)
    (hsparse : ¬ count > 8#u32)
    (hnext : Std.Usize.wrapping_add maskIndex 1#usize = next)
    (trace : SparseMaskValueTrace mask basis values valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values maskIndex =
      ok (cont (valuesOut, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
  rw [if_pos hactive, hread]
  simp only [bind_tc_ok]
  rw [hcount]
  simp only [bind_tc_ok]
  rw [if_neg hsparse, trace.sumRun]
  simp only [bind_tc_ok]
  rw [trace.half0Run]
  simp only [bind_tc_ok]
  rw [trace.half1Run]
  simp only [bind_tc_ok]
  rw [trace.half2Run]
  simp only [bind_tc_ok]
  rw [trace.half3Run]
  simp only [bind_tc_ok]
  rw [trace.pushRun]
  simp [hnext, Aeneas.Std.lift]

private theorem releasedMaskValueStep1
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (trace : DenseMaskValueTrace 0x1801#u16 basis total values valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values 1#usize =
      ok (cont (valuesOut, 2#usize)) := by
  apply releasedDenseMaskValueStep basis total values valuesOut
    1#usize 2#usize 0xe7fe#u16 0x1801#u16 13#u32
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.len, UScalar.lt_equiv]
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.index_usize]
  · rfl
  · decide
  · decide
  · exact usize_one_succ
  · exact trace

private theorem releasedMaskValueStep2
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (trace : DenseMaskValueTrace 0x1001#u16 basis total values valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values 2#usize =
      ok (cont (valuesOut, 3#usize)) := by
  apply releasedDenseMaskValueStep basis total values valuesOut
    2#usize 3#usize 0xeffe#u16 0x1001#u16 14#u32
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.len, UScalar.lt_equiv]
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.index_usize]
  · rfl
  · decide
  · decide
  · exact usize_two_succ
  · exact trace

private theorem releasedMaskValueStep3
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (trace : SparseMaskValueTrace 0x0000#u16 basis values valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values 3#usize =
      ok (cont (valuesOut, 4#usize)) := by
  apply releasedSparseMaskValueStep basis total values valuesOut
    3#usize 4#usize 0x0000#u16 0#u32
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.len, UScalar.lt_equiv]
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.index_usize]
  · rfl
  · decide
  · exact usize_three_succ
  · exact trace

private theorem releasedMaskValueStep4
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (trace : DenseMaskValueTrace 0x000f#u16 basis total values valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values 4#usize =
      ok (cont (valuesOut, 5#usize)) := by
  apply releasedDenseMaskValueStep basis total values valuesOut
    4#usize 5#usize 0xfff0#u16 0x000f#u16 12#u32
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.len, UScalar.lt_equiv]
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.index_usize]
  · rfl
  · decide
  · decide
  · exact usize_four_succ
  · exact trace

private theorem releasedMaskValueStep5
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (trace : DenseMaskValueTrace 0x0005#u16 basis total values valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values 5#usize =
      ok (cont (valuesOut, 6#usize)) := by
  apply releasedDenseMaskValueStep basis total values valuesOut
    5#usize 6#usize 0xfffa#u16 0x0005#u16 14#u32
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.len, UScalar.lt_equiv]
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.index_usize]
  · rfl
  · decide
  · decide
  · exact usize_five_succ
  · exact trace

private theorem releasedMaskValueStep6
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (trace : DenseMaskValueTrace 0x0000#u16 basis total values valuesOut) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values 6#usize =
      ok (cont (valuesOut, 7#usize)) := by
  apply releasedDenseMaskValueStep basis total values valuesOut
    6#usize 7#usize 0xffff#u16 0x0000#u16 16#u32
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.len, UScalar.lt_equiv]
  · simp [releasedMasks, alloc.vec.Vec.deref, Slice.index_usize]
  · rfl
  · decide
  · decide
  · exact usize_six_succ
  · exact trace

private theorem releasedMaskValueDone
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values : alloc.vec.Vec RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body
        (alloc.vec.Vec.deref releasedMasks) basis total values 7#usize =
      ok (done values) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5.body,
    releasedMasks, alloc.vec.Vec.deref, Slice.len, UScalar.lt_equiv]

/-- On the released seven masks, the extracted loop consumes exactly the six
dense-complement traces and the one sparse trace in wire order, and returns
exactly the seven values pushed by those traces. -/
theorem releasedMaskValuesLoopExact
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values0 values1 values2 values3 values4 values5 values6 values7 :
      alloc.vec.Vec RawQM31)
    (trace0 : DenseMaskValueTrace 0x1800#u16 basis total values0 values1)
    (trace1 : DenseMaskValueTrace 0x1801#u16 basis total values1 values2)
    (trace2 : DenseMaskValueTrace 0x1001#u16 basis total values2 values3)
    (trace3 : SparseMaskValueTrace 0x0000#u16 basis values3 values4)
    (trace4 : DenseMaskValueTrace 0x000f#u16 basis total values4 values5)
    (trace5 : DenseMaskValueTrace 0x0005#u16 basis total values5 values6)
    (trace6 : DenseMaskValueTrace 0x0000#u16 basis total values6 values7) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5
        (alloc.vec.Vec.deref releasedMasks) basis total values0 0#usize =
      ok values7 := by
  have step0 := releasedMaskValueStep0 basis total values0 values1 trace0
  have step1 := releasedMaskValueStep1 basis total values1 values2 trace1
  have step2 := releasedMaskValueStep2 basis total values2 values3 trace2
  have step3 := releasedMaskValueStep3 basis total values3 values4 trace3
  have step4 := releasedMaskValueStep4 basis total values4 values5 trace4
  have step5 := releasedMaskValueStep5 basis total values5 values6 trace5
  have step6 := releasedMaskValueStep6 basis total values6 values7 trace6
  have done := releasedMaskValueDone basis total values7
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks_loop5
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
  rw [done]

private theorem selectedZeroStep
    (basis : Array RawQM31 16#usize) (accumulator : RawQM31)
    (low next : Std.Usize) (hactive : low < 16#usize)
    (hnext : Std.Usize.wrapping_add low 1#usize = next) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
        0x0000#u16 basis accumulator low =
      ok (cont (accumulator, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
  rw [if_pos hactive]
  simp [hnext, Aeneas.Std.lift]

private theorem selectedBasisDone
    (selected : Std.U16) (basis : Array RawQM31 16#usize)
    (accumulator : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
        selected basis accumulator 16#usize =
      ok (done accumulator) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
  rw [if_neg (by decide)]

private theorem selectedBasisOffStep
    (selected : Std.U16) (basis : Array RawQM31 16#usize)
    (accumulator : RawQM31) (low next : Std.Usize) (bit : Std.U16)
    (hactive : low < 16#usize)
    (hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount low) = bit)
    (hoff : selected &&& bit = 0#u16)
    (hnext : Std.Usize.wrapping_add low 1#usize = next) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
        selected basis accumulator low =
      ok (cont (accumulator, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
  rw [if_pos hactive, hshift]
  simp only [lift, bind_tc_ok]
  rw [hoff, if_neg (by decide), hnext]

private theorem selectedBasisOnStep
    (selected : Std.U16) (basis : Array RawQM31 16#usize)
    (accumulator value accumulatorOut : RawQM31)
    (low next : Std.Usize) (bit : Std.U16)
    (hactive : low < 16#usize)
    (hshift : Std.U16.wrapping_shl 1#u16
      (V5RelationLinkedGenerated.usizeShiftCount low) = bit)
    (hon : selected &&& bit = bit)
    (hbit : bit != 0#u16)
    (hread : Array.index_usize basis low = ok value)
    (hadd :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add accumulator value =
        ok accumulatorOut)
    (hnext : Std.Usize.wrapping_add low 1#usize = next) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
        selected basis accumulator low =
      ok (cont (accumulatorOut, next)) := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
  rw [if_pos hactive, hshift]
  simp only [lift, bind_tc_ok]
  rw [hon, if_pos hbit, hread]
  simp only [bind_tc_ok]
  rw [hadd]
  simp only [bind_tc_ok, hnext]

private theorem selectedBit0 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 0#usize) = 0x0001#u16 := by
  exact oneShiftVia 0#usize 0#u32 0x0001#u16
    (usizeShiftCountEq 0#usize 0#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit1 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 1#usize) = 0x0002#u16 := by
  exact oneShiftVia 1#usize 1#u32 0x0002#u16
    (usizeShiftCountEq 1#usize 1#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit2 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 2#usize) = 0x0004#u16 := by
  exact oneShiftVia 2#usize 2#u32 0x0004#u16
    (usizeShiftCountEq 2#usize 2#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit3 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 3#usize) = 0x0008#u16 := by
  exact oneShiftVia 3#usize 3#u32 0x0008#u16
    (usizeShiftCountEq 3#usize 3#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit4 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 4#usize) = 0x0010#u16 := by
  exact oneShiftVia 4#usize 4#u32 0x0010#u16
    (usizeShiftCountEq 4#usize 4#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit5 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 5#usize) = 0x0020#u16 := by
  exact oneShiftVia 5#usize 5#u32 0x0020#u16
    (usizeShiftCountEq 5#usize 5#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit6 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 6#usize) = 0x0040#u16 := by
  exact oneShiftVia 6#usize 6#u32 0x0040#u16
    (usizeShiftCountEq 6#usize 6#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit7 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 7#usize) = 0x0080#u16 := by
  exact oneShiftVia 7#usize 7#u32 0x0080#u16
    (usizeShiftCountEq 7#usize 7#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit8 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 8#usize) = 0x0100#u16 := by
  exact oneShiftVia 8#usize 8#u32 0x0100#u16
    (usizeShiftCountEq 8#usize 8#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit9 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 9#usize) = 0x0200#u16 := by
  exact oneShiftVia 9#usize 9#u32 0x0200#u16
    (usizeShiftCountEq 9#usize 9#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit10 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 10#usize) = 0x0400#u16 := by
  exact oneShiftVia 10#usize 10#u32 0x0400#u16
    (usizeShiftCountEq 10#usize 10#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit11 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 11#usize) = 0x0800#u16 := by
  exact oneShiftVia 11#usize 11#u32 0x0800#u16
    (usizeShiftCountEq 11#usize 11#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit12 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 12#usize) = 0x1000#u16 := by
  exact oneShiftVia 12#usize 12#u32 0x1000#u16
    (usizeShiftCountEq 12#usize 12#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit13 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 13#usize) = 0x2000#u16 := by
  exact oneShiftVia 13#usize 13#u32 0x2000#u16
    (usizeShiftCountEq 13#usize 13#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit14 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 14#usize) = 0x4000#u16 := by
  exact oneShiftVia 14#usize 14#u32 0x4000#u16
    (usizeShiftCountEq 14#usize 14#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

private theorem selectedBit15 : Std.U16.wrapping_shl 1#u16
    (V5RelationLinkedGenerated.usizeShiftCount 15#usize) = 0x8000#u16 := by
  exact oneShiftVia 15#usize 15#u32 0x8000#u16
    (usizeShiftCountEq 15#usize 15#u32 (by decide) rfl)
    (by apply Std.U16.bv_eq_imp_eq; decide)

theorem selectedBasisStepsExact
    (selected : Std.U16) (basis : Array RawQM31 16#usize)
    (acc1 acc2 acc3 acc4 acc5 acc6 acc7 acc8 acc9 acc10 acc11 acc12 acc13
      acc14 acc15 acc16 : RawQM31)
    (step0 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
            0#usize = ok (cont (acc1, 1#usize)))
    (step1 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc1 1#usize = ok (cont (acc2, 2#usize)))
    (step2 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc2 2#usize = ok (cont (acc3, 3#usize)))
    (step3 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc3 3#usize = ok (cont (acc4, 4#usize)))
    (step4 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc4 4#usize = ok (cont (acc5, 5#usize)))
    (step5 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc5 5#usize = ok (cont (acc6, 6#usize)))
    (step6 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc6 6#usize = ok (cont (acc7, 7#usize)))
    (step7 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc7 7#usize = ok (cont (acc8, 8#usize)))
    (step8 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc8 8#usize = ok (cont (acc9, 9#usize)))
    (step9 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc9 9#usize = ok (cont (acc10, 10#usize)))
    (step10 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc10 10#usize = ok (cont (acc11, 11#usize)))
    (step11 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc11 11#usize = ok (cont (acc12, 12#usize)))
    (step12 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc12 12#usize = ok (cont (acc13, 13#usize)))
    (step13 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc13 13#usize = ok (cont (acc14, 14#usize)))
    (step14 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc14 14#usize = ok (cont (acc15, 15#usize)))
    (step15 :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
          selected basis acc15 15#usize = ok (cont (acc16, 16#usize))) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        selected basis = ok acc16 := by
  have done := selectedBasisDone selected basis acc16
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop
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
  dsimp only
  rw [step13]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step14]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step15]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [done]

private theorem releasedSelectedZeroExact
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        0x0000#u16 basis =
      ok V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO := by
  let zero := V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
  have step0 := selectedZeroStep basis zero 0#usize 1#usize (by decide)
    usize_zero_succ
  have step1 := selectedZeroStep basis zero 1#usize 2#usize (by decide)
    usize_one_succ
  have step2 := selectedZeroStep basis zero 2#usize 3#usize (by decide)
    usize_two_succ
  have step3 := selectedZeroStep basis zero 3#usize 4#usize (by decide)
    usize_three_succ
  have step4 := selectedZeroStep basis zero 4#usize 5#usize (by decide)
    usize_four_succ
  have step5 := selectedZeroStep basis zero 5#usize 6#usize (by decide)
    usize_five_succ
  have step6 := selectedZeroStep basis zero 6#usize 7#usize (by decide)
    usize_six_succ
  have step7 := selectedZeroStep basis zero 7#usize 8#usize (by decide)
    usize_seven_succ
  have step8 := selectedZeroStep basis zero 8#usize 9#usize (by decide)
    usize_eight_succ
  have step9 := selectedZeroStep basis zero 9#usize 10#usize (by decide)
    usize_nine_succ
  have step10 := selectedZeroStep basis zero 10#usize 11#usize (by decide)
    usize_ten_succ
  have step11 := selectedZeroStep basis zero 11#usize 12#usize (by decide)
    usize_eleven_succ
  have step12 := selectedZeroStep basis zero 12#usize 13#usize (by decide)
    usize_twelve_succ
  have step13 := selectedZeroStep basis zero 13#usize 14#usize (by decide)
    usize_thirteen_succ
  have step14 := selectedZeroStep basis zero 14#usize 15#usize (by decide)
    usize_fourteen_succ
  have step15 := selectedZeroStep basis zero 15#usize 16#usize (by decide)
    usize_fifteen_succ
  have done := selectedBasisDone 0x0000#u16 basis zero
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop
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
  dsimp only
  rw [step13]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step14]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [step15]
  simp only
  rw [loop.eq_1]
  dsimp only [zero]
  rw [done]

theorem releasedSelected1800Exact
    (alpha0Cubed alpha0Squared alpha0 alpha1SquaredTimesAlpha0 alpha1
      sum11 sum12 : RawQM31)
    (hadd11 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
          alpha1SquaredTimesAlpha0 = ok sum11)
    (hadd12 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum11 alpha1 =
        ok sum12) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        0x1800#u16
        (releasedBasis alpha0Cubed alpha0Squared alpha0
          alpha1SquaredTimesAlpha0 alpha1) = ok sum12 := by
  let basis := releasedBasis alpha0Cubed alpha0Squared alpha0
    alpha1SquaredTimesAlpha0 alpha1
  let zero := V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
  have step0 := selectedBasisOffStep 0x1800#u16 basis zero
    0#usize 1#usize 0x0001#u16 (by decide) selectedBit0 (by decide)
    usize_zero_succ
  have step1 := selectedBasisOffStep 0x1800#u16 basis zero
    1#usize 2#usize 0x0002#u16 (by decide) selectedBit1 (by decide)
    usize_one_succ
  have step2 := selectedBasisOffStep 0x1800#u16 basis zero
    2#usize 3#usize 0x0004#u16 (by decide) selectedBit2 (by decide)
    usize_two_succ
  have step3 := selectedBasisOffStep 0x1800#u16 basis zero
    3#usize 4#usize 0x0008#u16 (by decide) selectedBit3 (by decide)
    usize_three_succ
  have step4 := selectedBasisOffStep 0x1800#u16 basis zero
    4#usize 5#usize 0x0010#u16 (by decide) selectedBit4 (by decide)
    usize_four_succ
  have step5 := selectedBasisOffStep 0x1800#u16 basis zero
    5#usize 6#usize 0x0020#u16 (by decide) selectedBit5 (by decide)
    usize_five_succ
  have step6 := selectedBasisOffStep 0x1800#u16 basis zero
    6#usize 7#usize 0x0040#u16 (by decide) selectedBit6 (by decide)
    usize_six_succ
  have step7 := selectedBasisOffStep 0x1800#u16 basis zero
    7#usize 8#usize 0x0080#u16 (by decide) selectedBit7 (by decide)
    usize_seven_succ
  have step8 := selectedBasisOffStep 0x1800#u16 basis zero
    8#usize 9#usize 0x0100#u16 (by decide) selectedBit8 (by decide)
    usize_eight_succ
  have step9 := selectedBasisOffStep 0x1800#u16 basis zero
    9#usize 10#usize 0x0200#u16 (by decide) selectedBit9 (by decide)
    usize_nine_succ
  have step10 := selectedBasisOffStep 0x1800#u16 basis zero
    10#usize 11#usize 0x0400#u16 (by decide) selectedBit10 (by decide)
    usize_ten_succ
  have step11 := selectedBasisOnStep 0x1800#u16 basis zero
    alpha1SquaredTimesAlpha0 sum11 11#usize 12#usize 0x0800#u16
    (by decide) selectedBit11 (by decide) (by decide) (by rfl) hadd11
    usize_eleven_succ
  have step12 := selectedBasisOnStep 0x1800#u16 basis sum11 alpha1 sum12
    12#usize 13#usize 0x1000#u16 (by decide) selectedBit12 (by decide)
    (by decide) (by rfl) hadd12 usize_twelve_succ
  have step13 := selectedBasisOffStep 0x1800#u16 basis sum12
    13#usize 14#usize 0x2000#u16 (by decide) selectedBit13 (by decide)
    usize_thirteen_succ
  have step14 := selectedBasisOffStep 0x1800#u16 basis sum12
    14#usize 15#usize 0x4000#u16 (by decide) selectedBit14 (by decide)
    usize_fourteen_succ
  have step15 := selectedBasisOffStep 0x1800#u16 basis sum12
    15#usize 16#usize 0x8000#u16 (by decide) selectedBit15 (by decide)
    usize_fifteen_succ
  exact selectedBasisStepsExact 0x1800#u16 basis
    zero zero zero zero zero zero zero zero zero zero zero sum11 sum12 sum12
      sum12 sum12
    step0 step1 step2 step3 step4 step5 step6 step7 step8 step9 step10
      step11 step12 step13 step14 step15

theorem releasedSelected1801Exact
    (alpha0Cubed alpha0Squared alpha0 alpha1SquaredTimesAlpha0 alpha1
      sum0 sum11 sum12 : RawQM31)
    (hadd0 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = ok sum0)
    (hadd11 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          sum0 alpha1SquaredTimesAlpha0 = ok sum11)
    (hadd12 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum11 alpha1 =
        ok sum12) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        0x1801#u16
        (releasedBasis alpha0Cubed alpha0Squared alpha0
          alpha1SquaredTimesAlpha0 alpha1) = ok sum12 := by
  let basis := releasedBasis alpha0Cubed alpha0Squared alpha0
    alpha1SquaredTimesAlpha0 alpha1
  let zero := V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
  have step0 := selectedBasisOnStep 0x1801#u16 basis zero
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE sum0
    0#usize 1#usize 0x0001#u16 (by decide) selectedBit0 (by decide)
    (by decide) (by rfl) hadd0 usize_zero_succ
  have step1 := selectedBasisOffStep 0x1801#u16 basis sum0
    1#usize 2#usize 0x0002#u16 (by decide) selectedBit1 (by decide)
    usize_one_succ
  have step2 := selectedBasisOffStep 0x1801#u16 basis sum0
    2#usize 3#usize 0x0004#u16 (by decide) selectedBit2 (by decide)
    usize_two_succ
  have step3 := selectedBasisOffStep 0x1801#u16 basis sum0
    3#usize 4#usize 0x0008#u16 (by decide) selectedBit3 (by decide)
    usize_three_succ
  have step4 := selectedBasisOffStep 0x1801#u16 basis sum0
    4#usize 5#usize 0x0010#u16 (by decide) selectedBit4 (by decide)
    usize_four_succ
  have step5 := selectedBasisOffStep 0x1801#u16 basis sum0
    5#usize 6#usize 0x0020#u16 (by decide) selectedBit5 (by decide)
    usize_five_succ
  have step6 := selectedBasisOffStep 0x1801#u16 basis sum0
    6#usize 7#usize 0x0040#u16 (by decide) selectedBit6 (by decide)
    usize_six_succ
  have step7 := selectedBasisOffStep 0x1801#u16 basis sum0
    7#usize 8#usize 0x0080#u16 (by decide) selectedBit7 (by decide)
    usize_seven_succ
  have step8 := selectedBasisOffStep 0x1801#u16 basis sum0
    8#usize 9#usize 0x0100#u16 (by decide) selectedBit8 (by decide)
    usize_eight_succ
  have step9 := selectedBasisOffStep 0x1801#u16 basis sum0
    9#usize 10#usize 0x0200#u16 (by decide) selectedBit9 (by decide)
    usize_nine_succ
  have step10 := selectedBasisOffStep 0x1801#u16 basis sum0
    10#usize 11#usize 0x0400#u16 (by decide) selectedBit10 (by decide)
    usize_ten_succ
  have step11 := selectedBasisOnStep 0x1801#u16 basis sum0
    alpha1SquaredTimesAlpha0 sum11 11#usize 12#usize 0x0800#u16
    (by decide) selectedBit11 (by decide) (by decide) (by rfl) hadd11
    usize_eleven_succ
  have step12 := selectedBasisOnStep 0x1801#u16 basis sum11 alpha1 sum12
    12#usize 13#usize 0x1000#u16 (by decide) selectedBit12 (by decide)
    (by decide) (by rfl) hadd12 usize_twelve_succ
  have step13 := selectedBasisOffStep 0x1801#u16 basis sum12
    13#usize 14#usize 0x2000#u16 (by decide) selectedBit13 (by decide)
    usize_thirteen_succ
  have step14 := selectedBasisOffStep 0x1801#u16 basis sum12
    14#usize 15#usize 0x4000#u16 (by decide) selectedBit14 (by decide)
    usize_fourteen_succ
  have step15 := selectedBasisOffStep 0x1801#u16 basis sum12
    15#usize 16#usize 0x8000#u16 (by decide) selectedBit15 (by decide)
    usize_fifteen_succ
  exact selectedBasisStepsExact 0x1801#u16 basis
    sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum11 sum12
      sum12 sum12 sum12
    step0 step1 step2 step3 step4 step5 step6 step7 step8 step9 step10
      step11 step12 step13 step14 step15

theorem releasedSelected1001Exact
    (alpha0Cubed alpha0Squared alpha0 alpha1SquaredTimesAlpha0 alpha1
      sum0 sum12 : RawQM31)
    (hadd0 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = ok sum0)
    (hadd12 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 alpha1 =
        ok sum12) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        0x1001#u16
        (releasedBasis alpha0Cubed alpha0Squared alpha0
          alpha1SquaredTimesAlpha0 alpha1) = ok sum12 := by
  let basis := releasedBasis alpha0Cubed alpha0Squared alpha0
    alpha1SquaredTimesAlpha0 alpha1
  let zero := V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
  have step0 := selectedBasisOnStep 0x1001#u16 basis zero
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE sum0
    0#usize 1#usize 0x0001#u16 (by decide) selectedBit0 (by decide)
    (by decide) (by rfl) hadd0 usize_zero_succ
  have step1 := selectedBasisOffStep 0x1001#u16 basis sum0
    1#usize 2#usize 0x0002#u16 (by decide) selectedBit1 (by decide)
    usize_one_succ
  have step2 := selectedBasisOffStep 0x1001#u16 basis sum0
    2#usize 3#usize 0x0004#u16 (by decide) selectedBit2 (by decide)
    usize_two_succ
  have step3 := selectedBasisOffStep 0x1001#u16 basis sum0
    3#usize 4#usize 0x0008#u16 (by decide) selectedBit3 (by decide)
    usize_three_succ
  have step4 := selectedBasisOffStep 0x1001#u16 basis sum0
    4#usize 5#usize 0x0010#u16 (by decide) selectedBit4 (by decide)
    usize_four_succ
  have step5 := selectedBasisOffStep 0x1001#u16 basis sum0
    5#usize 6#usize 0x0020#u16 (by decide) selectedBit5 (by decide)
    usize_five_succ
  have step6 := selectedBasisOffStep 0x1001#u16 basis sum0
    6#usize 7#usize 0x0040#u16 (by decide) selectedBit6 (by decide)
    usize_six_succ
  have step7 := selectedBasisOffStep 0x1001#u16 basis sum0
    7#usize 8#usize 0x0080#u16 (by decide) selectedBit7 (by decide)
    usize_seven_succ
  have step8 := selectedBasisOffStep 0x1001#u16 basis sum0
    8#usize 9#usize 0x0100#u16 (by decide) selectedBit8 (by decide)
    usize_eight_succ
  have step9 := selectedBasisOffStep 0x1001#u16 basis sum0
    9#usize 10#usize 0x0200#u16 (by decide) selectedBit9 (by decide)
    usize_nine_succ
  have step10 := selectedBasisOffStep 0x1001#u16 basis sum0
    10#usize 11#usize 0x0400#u16 (by decide) selectedBit10 (by decide)
    usize_ten_succ
  have step11 := selectedBasisOffStep 0x1001#u16 basis sum0
    11#usize 12#usize 0x0800#u16 (by decide) selectedBit11 (by decide)
    usize_eleven_succ
  have step12 := selectedBasisOnStep 0x1001#u16 basis sum0 alpha1 sum12
    12#usize 13#usize 0x1000#u16 (by decide) selectedBit12 (by decide)
    (by decide) (by rfl) hadd12 usize_twelve_succ
  have step13 := selectedBasisOffStep 0x1001#u16 basis sum12
    13#usize 14#usize 0x2000#u16 (by decide) selectedBit13 (by decide)
    usize_thirteen_succ
  have step14 := selectedBasisOffStep 0x1001#u16 basis sum12
    14#usize 15#usize 0x4000#u16 (by decide) selectedBit14 (by decide)
    usize_fourteen_succ
  have step15 := selectedBasisOffStep 0x1001#u16 basis sum12
    15#usize 16#usize 0x8000#u16 (by decide) selectedBit15 (by decide)
    usize_fifteen_succ
  exact selectedBasisStepsExact 0x1001#u16 basis
    sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum0 sum12
      sum12 sum12 sum12
    step0 step1 step2 step3 step4 step5 step6 step7 step8 step9 step10
      step11 step12 step13 step14 step15

theorem releasedSelected000fExact
    (alpha0Cubed alpha0Squared alpha0 alpha1SquaredTimesAlpha0 alpha1
      sum0 sum1 sum2 sum3 : RawQM31)
    (hadd0 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = ok sum0)
    (hadd1 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 alpha0Cubed =
        ok sum1)
    (hadd2 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 alpha0Squared =
        ok sum2)
    (hadd3 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum2 alpha0 =
        ok sum3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        0x000f#u16
        (releasedBasis alpha0Cubed alpha0Squared alpha0
          alpha1SquaredTimesAlpha0 alpha1) = ok sum3 := by
  let basis := releasedBasis alpha0Cubed alpha0Squared alpha0
    alpha1SquaredTimesAlpha0 alpha1
  let zero := V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
  have step0 := selectedBasisOnStep 0x000f#u16 basis zero
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE sum0
    0#usize 1#usize 0x0001#u16 (by decide) selectedBit0 (by decide)
    (by decide) (by rfl) hadd0 usize_zero_succ
  have step1 := selectedBasisOnStep 0x000f#u16 basis sum0 alpha0Cubed sum1
    1#usize 2#usize 0x0002#u16 (by decide) selectedBit1 (by decide)
    (by decide) (by rfl) hadd1 usize_one_succ
  have step2 := selectedBasisOnStep 0x000f#u16 basis sum1 alpha0Squared sum2
    2#usize 3#usize 0x0004#u16 (by decide) selectedBit2 (by decide)
    (by decide) (by rfl) hadd2 usize_two_succ
  have step3 := selectedBasisOnStep 0x000f#u16 basis sum2 alpha0 sum3
    3#usize 4#usize 0x0008#u16 (by decide) selectedBit3 (by decide)
    (by decide) (by rfl) hadd3 usize_three_succ
  have step4 := selectedBasisOffStep 0x000f#u16 basis sum3
    4#usize 5#usize 0x0010#u16 (by decide) selectedBit4 (by decide)
    usize_four_succ
  have step5 := selectedBasisOffStep 0x000f#u16 basis sum3
    5#usize 6#usize 0x0020#u16 (by decide) selectedBit5 (by decide)
    usize_five_succ
  have step6 := selectedBasisOffStep 0x000f#u16 basis sum3
    6#usize 7#usize 0x0040#u16 (by decide) selectedBit6 (by decide)
    usize_six_succ
  have step7 := selectedBasisOffStep 0x000f#u16 basis sum3
    7#usize 8#usize 0x0080#u16 (by decide) selectedBit7 (by decide)
    usize_seven_succ
  have step8 := selectedBasisOffStep 0x000f#u16 basis sum3
    8#usize 9#usize 0x0100#u16 (by decide) selectedBit8 (by decide)
    usize_eight_succ
  have step9 := selectedBasisOffStep 0x000f#u16 basis sum3
    9#usize 10#usize 0x0200#u16 (by decide) selectedBit9 (by decide)
    usize_nine_succ
  have step10 := selectedBasisOffStep 0x000f#u16 basis sum3
    10#usize 11#usize 0x0400#u16 (by decide) selectedBit10 (by decide)
    usize_ten_succ
  have step11 := selectedBasisOffStep 0x000f#u16 basis sum3
    11#usize 12#usize 0x0800#u16 (by decide) selectedBit11 (by decide)
    usize_eleven_succ
  have step12 := selectedBasisOffStep 0x000f#u16 basis sum3
    12#usize 13#usize 0x1000#u16 (by decide) selectedBit12 (by decide)
    usize_twelve_succ
  have step13 := selectedBasisOffStep 0x000f#u16 basis sum3
    13#usize 14#usize 0x2000#u16 (by decide) selectedBit13 (by decide)
    usize_thirteen_succ
  have step14 := selectedBasisOffStep 0x000f#u16 basis sum3
    14#usize 15#usize 0x4000#u16 (by decide) selectedBit14 (by decide)
    usize_fourteen_succ
  have step15 := selectedBasisOffStep 0x000f#u16 basis sum3
    15#usize 16#usize 0x8000#u16 (by decide) selectedBit15 (by decide)
    usize_fifteen_succ
  exact selectedBasisStepsExact 0x000f#u16 basis
    sum0 sum1 sum2 sum3 sum3 sum3 sum3 sum3 sum3 sum3 sum3 sum3 sum3 sum3
      sum3 sum3
    step0 step1 step2 step3 step4 step5 step6 step7 step8 step9 step10
      step11 step12 step13 step14 step15

theorem releasedSelected0005Exact
    (alpha0Cubed alpha0Squared alpha0 alpha1SquaredTimesAlpha0 alpha1
      sum0 sum2 : RawQM31)
    (hadd0 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = ok sum0)
    (hadd2 :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 alpha0Squared =
        ok sum2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        0x0005#u16
        (releasedBasis alpha0Cubed alpha0Squared alpha0
          alpha1SquaredTimesAlpha0 alpha1) = ok sum2 := by
  let basis := releasedBasis alpha0Cubed alpha0Squared alpha0
    alpha1SquaredTimesAlpha0 alpha1
  let zero := V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
  have step0 := selectedBasisOnStep 0x0005#u16 basis zero
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE sum0
    0#usize 1#usize 0x0001#u16 (by decide) selectedBit0 (by decide)
    (by decide) (by rfl) hadd0 usize_zero_succ
  have step1 := selectedBasisOffStep 0x0005#u16 basis sum0
    1#usize 2#usize 0x0002#u16 (by decide) selectedBit1 (by decide)
    usize_one_succ
  have step2 := selectedBasisOnStep 0x0005#u16 basis sum0 alpha0Squared sum2
    2#usize 3#usize 0x0004#u16 (by decide) selectedBit2 (by decide)
    (by decide) (by rfl) hadd2 usize_two_succ
  have step3 := selectedBasisOffStep 0x0005#u16 basis sum2
    3#usize 4#usize 0x0008#u16 (by decide) selectedBit3 (by decide)
    usize_three_succ
  have step4 := selectedBasisOffStep 0x0005#u16 basis sum2
    4#usize 5#usize 0x0010#u16 (by decide) selectedBit4 (by decide)
    usize_four_succ
  have step5 := selectedBasisOffStep 0x0005#u16 basis sum2
    5#usize 6#usize 0x0020#u16 (by decide) selectedBit5 (by decide)
    usize_five_succ
  have step6 := selectedBasisOffStep 0x0005#u16 basis sum2
    6#usize 7#usize 0x0040#u16 (by decide) selectedBit6 (by decide)
    usize_six_succ
  have step7 := selectedBasisOffStep 0x0005#u16 basis sum2
    7#usize 8#usize 0x0080#u16 (by decide) selectedBit7 (by decide)
    usize_seven_succ
  have step8 := selectedBasisOffStep 0x0005#u16 basis sum2
    8#usize 9#usize 0x0100#u16 (by decide) selectedBit8 (by decide)
    usize_eight_succ
  have step9 := selectedBasisOffStep 0x0005#u16 basis sum2
    9#usize 10#usize 0x0200#u16 (by decide) selectedBit9 (by decide)
    usize_nine_succ
  have step10 := selectedBasisOffStep 0x0005#u16 basis sum2
    10#usize 11#usize 0x0400#u16 (by decide) selectedBit10 (by decide)
    usize_ten_succ
  have step11 := selectedBasisOffStep 0x0005#u16 basis sum2
    11#usize 12#usize 0x0800#u16 (by decide) selectedBit11 (by decide)
    usize_eleven_succ
  have step12 := selectedBasisOffStep 0x0005#u16 basis sum2
    12#usize 13#usize 0x1000#u16 (by decide) selectedBit12 (by decide)
    usize_twelve_succ
  have step13 := selectedBasisOffStep 0x0005#u16 basis sum2
    13#usize 14#usize 0x2000#u16 (by decide) selectedBit13 (by decide)
    usize_thirteen_succ
  have step14 := selectedBasisOffStep 0x0005#u16 basis sum2
    14#usize 15#usize 0x4000#u16 (by decide) selectedBit14 (by decide)
    usize_fourteen_succ
  have step15 := selectedBasisOffStep 0x0005#u16 basis sum2
    15#usize 16#usize 0x8000#u16 (by decide) selectedBit15 (by decide)
    usize_fifteen_succ
  exact selectedBasisStepsExact 0x0005#u16 basis
    sum0 sum0 sum2 sum2 sum2 sum2 sum2 sum2 sum2 sum2 sum2 sum2 sum2 sum2
      sum2 sum2
    step0 step1 step2 step3 step4 step5 step6 step7 step8 step9 step10
      step11 step12 step13 step14 step15

structure ReleasedBinaryPowerTrace (alpha0 alpha1 : RawQM31) where
  alpha0Squared : RawQM31
  alpha1Squared : RawQM31
  alpha0Cubed : RawQM31
  alpha1Cubed : RawQM31
  cross : RawQM31
  square0Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.square alpha0 =
      ok alpha0Squared
  square1Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.square alpha1 =
      ok alpha1Squared
  cube0Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha0Squared alpha0 =
      ok alpha0Cubed
  cube1Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha1Squared alpha1 =
      ok alpha1Cubed
  crossRun :
    V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha1Squared alpha0 =
      ok cross
  alpha0Total0 : RawQM31
  alpha0Total1 : RawQM31
  alpha0Total2 : RawQM31
  alpha0Total3 : RawQM31
  alpha1Total0 : RawQM31
  alpha1Total1 : RawQM31
  alpha1Total2 : RawQM31
  alpha1Total3 : RawQM31
  add00Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = ok alpha0Total0
  add10Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = ok alpha1Total0
  add01Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
        alpha0Total0 alpha0Cubed = ok alpha0Total1
  add11Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
        alpha1Total0 alpha1Cubed = ok alpha1Total1
  add02Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
        alpha0Total1 alpha0Squared = ok alpha0Total2
  add12Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
        alpha1Total1 alpha1Squared = ok alpha1Total2
  add03Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
        alpha0Total2 alpha0 = ok alpha0Total3
  add13Run :
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
        alpha1Total2 alpha1 = ok alpha1Total3
  total : RawQM31
  totalRun :
    V5RelationLinkedGenerated.aspis_core.field.QM31.mul
        alpha0Total3 alpha1Total3 = ok total

structure ReleasedMaskValuesTrace
    (basis : Array RawQM31 16#usize) (total : RawQM31) where
  values0 : alloc.vec.Vec RawQM31
  values1 : alloc.vec.Vec RawQM31
  values2 : alloc.vec.Vec RawQM31
  values3 : alloc.vec.Vec RawQM31
  values4 : alloc.vec.Vec RawQM31
  values5 : alloc.vec.Vec RawQM31
  values6 : alloc.vec.Vec RawQM31
  values7 : alloc.vec.Vec RawQM31
  initial : values0 = alloc.vec.Vec.with_capacity RawQM31
    (Slice.len (alloc.vec.Vec.deref releasedMasks))
  trace0 : DenseMaskValueTrace 0x1800#u16 basis total values0 values1
  trace1 : DenseMaskValueTrace 0x1801#u16 basis total values1 values2
  trace2 : DenseMaskValueTrace 0x1001#u16 basis total values2 values3
  trace3 : SparseMaskValueTrace 0x0000#u16 basis values3 values4
  trace4 : DenseMaskValueTrace 0x000f#u16 basis total values4 values5
  trace5 : DenseMaskValueTrace 0x0005#u16 basis total values5 values6
  trace6 : DenseMaskValueTrace 0x0000#u16 basis total values6 values7

/-- Exact fixed-release source theorem for the optimized seven-mask helper.
All loops beneath the public function have already been discharged above; the
only inputs here are the explicit primitive field traces and vector pushes. -/
theorem releasedFoldBinaryLowMasksSourceExact
    (alpha0 alpha1 : RawQM31) (power : ReleasedBinaryPowerTrace alpha0 alpha1)
    (values : ReleasedMaskValuesTrace
      (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0 power.cross
        alpha1) power.total) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks
        (alloc.vec.Vec.deref releasedMasks) alpha0 alpha1 =
      ok values.values7 := by
  have basisRun := releasedBasisLoopExact alpha0 power.alpha0Squared
    power.alpha0Cubed alpha1 power.alpha1Squared power.alpha1Cubed power.cross
    power.crossRun
  have totalsRun := releasedPowerTotalsLoopExact alpha0 power.alpha0Squared
    power.alpha0Cubed alpha1 power.alpha1Squared power.alpha1Cubed
    power.alpha0Total0 power.alpha0Total1 power.alpha0Total2 power.alpha0Total3
    power.alpha1Total0 power.alpha1Total1 power.alpha1Total2 power.alpha1Total3
    power.add00Run power.add10Run power.add01Run power.add11Run power.add02Run
    power.add12Run power.add03Run power.add13Run
  have valuesRun := releasedMaskValuesLoopExact
    (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0 power.cross
      alpha1) power.total
    values.values0 values.values1 values.values2 values.values3 values.values4
      values.values5 values.values6 values.values7
    values.trace0 values.trace1 values.trace2 values.trace3 values.trace4
      values.trace5 values.trace6
  simp only [releasedAlpha0Powers, releasedAlpha1Powers, releasedBasis0] at basisRun totalsRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks
  rw [power.square0Run]
  simp only [bind_tc_ok]
  rw [power.square1Run]
  simp only [bind_tc_ok]
  rw [power.cube0Run]
  simp only [bind_tc_ok]
  rw [power.cube1Run]
  simp only [bind_tc_ok]
  rw [releasedMaskScanExact]
  simp only [bind_tc_ok]
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks.CROSS_POSITIONS,
    Aeneas.Std.lift]
  rw [basisRun]
  simp only [bind_tc_ok]
  rw [totalsRun]
  simp only [bind_tc_ok]
  rw [power.totalRun]
  simp only [bind_tc_ok]
  rw [← values.initial]
  exact valuesRun

end AspisV5RelationLinkedGroupedFold
