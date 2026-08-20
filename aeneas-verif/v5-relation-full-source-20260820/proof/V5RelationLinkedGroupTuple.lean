import V5RelationLinkedGroupedRows

namespace AspisV5RelationLinkedGroupTuple

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedFoldArithmetic

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

deriving instance Inhabited for V5RelationLinkedGenerated.aspis_core.field.CM31
deriving instance Inhabited for V5RelationLinkedGenerated.aspis_core.field.QM31

private theorem oneCanonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ONE := by
  norm_num [CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem zeroCanonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO := by
  norm_num [CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    AspisAeneasCM31Multiplicative.m31Modulus]

def allSameProgram
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) : Result RawQM31 := do
  let coefficient1 ←
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
  let coefficient2 ←
    V5RelationLinkedGenerated.aspis_core.field.QM31.add coefficient1 alpha2
  let coefficient3 ←
    V5RelationLinkedGenerated.aspis_core.field.QM31.add coefficient2 alpha
  let value ← Slice.index_usize groupValues (UScalar.cast .Usize group)
  let contribution ←
    V5RelationLinkedGenerated.aspis_core.field.QM31.mul value coefficient3
  let folded ←
    V5RelationLinkedGenerated.aspis_core.field.QM31.add
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution
  let half1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half folded
  V5RelationLinkedGenerated.aspis_core.field.QM31.half half1

def groupsAllSame (group : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group, group, group, group]

private def powers
    (alpha alpha2 alpha3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    alpha3, alpha2, alpha]

private def unique0 : Array Std.U8 4#usize :=
  Array.repeat 4#usize 0#u8

private def unique1 (group : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group, 0#u8, 0#u8, 0#u8]

private def coefficients0 : Array RawQM31 4#usize :=
  Array.repeat 4#usize V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO

private def coefficients1 : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def coefficientsAt (coefficient : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def countsAt (count : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [count, 0#u8, 0#u8, 0#u8]

private def slots0 : Array Std.U8 4#usize :=
  Array.repeat 4#usize 0#u8

private def rangeFrom (start : Std.Usize) : core.ops.range.Range Std.Usize :=
  { start, «end» := 4#usize }

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have getExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simp [hbound]
  simpa [valueEq, getExact] using run

private theorem arrayMake4Index0
    {T : Type} [Inhabited T] (a b c d : T) :
    Array.index_usize (Array.make 4#usize [a, b, c, d]) 0#usize = ok a := by
  have run := arrayIndexRun (Array.make 4#usize [a, b, c, d]) 0#usize
    (by decide)
  change Array.index_usize (Array.make 4#usize [a, b, c, d]) 0#usize =
    ok (([a, b, c, d] : List T)[0]!) at run
  exact run

private theorem arrayMake4Index1
    {T : Type} [Inhabited T] (a b c d : T) :
    Array.index_usize (Array.make 4#usize [a, b, c, d]) 1#usize = ok b := by
  have run := arrayIndexRun (Array.make 4#usize [a, b, c, d]) 1#usize
    (by decide)
  change Array.index_usize (Array.make 4#usize [a, b, c, d]) 1#usize =
    ok (([a, b, c, d] : List T)[1]!) at run
  exact run

private theorem arrayMake4Index2
    {T : Type} [Inhabited T] (a b c d : T) :
    Array.index_usize (Array.make 4#usize [a, b, c, d]) 2#usize = ok c := by
  have run := arrayIndexRun (Array.make 4#usize [a, b, c, d]) 2#usize
    (by decide)
  change Array.index_usize (Array.make 4#usize [a, b, c, d]) 2#usize =
    ok (([a, b, c, d] : List T)[2]!) at run
  exact run

private theorem arrayMake4Index3
    {T : Type} [Inhabited T] (a b c d : T) :
    Array.index_usize (Array.make 4#usize [a, b, c, d]) 3#usize = ok d := by
  have run := arrayIndexRun (Array.make 4#usize [a, b, c, d]) 3#usize
    (by decide)
  change Array.index_usize (Array.make 4#usize [a, b, c, d]) 3#usize =
    ok (([a, b, c, d] : List T)[3]!) at run
  exact run

private theorem rangeNext0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 4#usize } =
      ok (some 0#usize, { start := 1#usize, «end» := 4#usize }) := by
  have hmax : 0 < UScalar.max .Usize := by
    have h := (1#usize).hBounds
    scalar_tac
  simp [rangeFrom, core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 4#usize } =
      ok (some 1#usize, { start := 2#usize, «end» := 4#usize }) := by
  have hmax : 1 < UScalar.max .Usize := by
    have h := (2#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := 4#usize } =
      ok (some 2#usize, { start := 3#usize, «end» := 4#usize }) := by
  have hmax : 2 < UScalar.max .Usize := by
    have h := (3#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 3#usize, «end» := 4#usize } =
      ok (some 3#usize, { start := 4#usize, «end» := 4#usize }) := by
  have hmax : 3 < UScalar.max .Usize := by
    have h := (4#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeDone4 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 4#usize, «end» := 4#usize } =
      ok (none, { start := 4#usize, «end» := 4#usize }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

private theorem rangeNext0End1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 1#usize } =
      ok (some 0#usize, { start := 1#usize, «end» := 1#usize }) := by
  have hmax : 0 < UScalar.max .Usize := by
    have h := (1#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeDone1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 1#usize } =
      ok (none, { start := 1#usize, «end» := 1#usize }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

private theorem allSameFindEmpty (group : Std.U8) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (Array.repeat 4#usize 0#u8) 0#usize group 0#usize = ok 0#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    UScalar.lt_equiv]

private theorem allSameFindExisting (group : Std.U8) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (unique1 group) 1#usize group 0#usize = ok 0#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
  rw [if_pos (by decide : (0#usize : Std.Usize) < 1#usize)]
  have hindex : Array.index_usize (unique1 group) 0#usize = ok group := by
    have run := arrayIndexRun (unique1 group) 0#usize (by decide)
    have valueExact : (unique1 group).val[0]! = group := by
      change ([group, 0#u8, 0#u8, 0#u8] : List Std.U8)[0]! = group
      rfl
    change Array.index_usize (unique1 group) 0#usize =
      ok ((unique1 group).val[0]!) at run
    rw [valueExact] at run
    exact run
  rw [hindex]
  simp

private theorem usizeZeroSucc :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (1#usize).hSize; scalar_tac)]
  norm_num

private theorem castUsizeZeroU8 :
    UScalar.cast .U8 0#usize = 0#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl

private theorem fromU8ToUsizeExact (value : Std.U8) :
    core.convert.num.FromUsizeU8.from value = UScalar.cast .Usize value := by
  apply UScalar.val_eq_imp
  rw [core.convert.num.FromUsizeU8.from_val_eq, UScalar.cast_val_eq]
  rw [Nat.mod_eq_of_lt]
  have h := value.hBounds
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [UScalarTy.numBits, hbits] at h ⊢ <;> omega

private theorem u8OneSucc : Std.U8.wrapping_add 1#u8 1#u8 = 2#u8 := by
  apply UScalar.val_eq_imp
  rw [Std.U8.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#u8).hSize; scalar_tac)]
  norm_num

private theorem u8TwoSucc : Std.U8.wrapping_add 2#u8 1#u8 = 3#u8 := by
  apply UScalar.val_eq_imp
  rw [Std.U8.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#u8).hSize; scalar_tac)]
  norm_num

private theorem u8ThreeSucc : Std.U8.wrapping_add 3#u8 1#u8 = 4#u8 := by
  apply UScalar.val_eq_imp
  rw [Std.U8.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#u8).hSize; scalar_tac)]
  norm_num

private theorem allSameOuterStep0
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 0#usize) unique0 coefficients0 unique0 slots0
        0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeNext0, allSameFindEmpty,
    groupsAllSame, powers, rangeFrom, unique0, unique1, coefficients0,
    coefficients1, countsAt, slots0, loop.eq_1, Array.index_usize,
    Array.update, UScalar.lt_equiv, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rw [castUsizeZeroU8]
    rfl
  · exact usizeZeroSucc

private theorem allSameOuterStep1
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient1 : RawQM31)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 1#usize) (unique1 group) coefficients1 (countsAt 1#u8)
        slots0 1#usize =
      ok (cont (rangeFrom 2#usize, unique1 group,
        coefficientsAt coefficient1, countsAt 2#u8, slots0, 1#usize)) := by
  have groupRun : Array.index_usize (groupsAllSame group) 1#usize =
      ok group := by
    simpa [groupsAllSame] using
      (arrayMake4Index1 group group group group)
  have coefficientRun : Array.index_usize coefficients1 0#usize =
      ok V5RelationLinkedGenerated.aspis_core.field.QM31.ONE := by
    simpa [coefficients1] using
      (arrayMake4Index0
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 1#usize =
      ok alpha3 := by
    simpa [powers] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize (countsAt 1#u8) 0#usize = ok 1#u8 := by
    simpa [countsAt] using
      (arrayMake4Index0 1#u8 0#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun, allSameFindExisting, coefficientRun, powerRun,
    coefficient1Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, coefficientsAt, countsAt, slots0,
    Array.update, Std.lift]
  constructor <;> apply Subtype.ext <;> rfl

private theorem allSameOuterStep2
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient1 coefficient2 : RawQM31)
    (coefficient2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          coefficient1 alpha2 = ok coefficient2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 2#usize) (unique1 group) (coefficientsAt coefficient1)
        (countsAt 2#u8) slots0 1#usize =
      ok (cont (rangeFrom 3#usize, unique1 group,
        coefficientsAt coefficient2, countsAt 3#u8, slots0, 1#usize)) := by
  have groupRun : Array.index_usize (groupsAllSame group) 2#usize =
      ok group := by
    simpa [groupsAllSame] using
      (arrayMake4Index2 group group group group)
  have coefficientRun :
      Array.index_usize (coefficientsAt coefficient1) 0#usize =
        ok coefficient1 := by
    simpa [coefficientsAt] using
      (arrayMake4Index0 coefficient1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize (countsAt 2#u8) 0#usize = ok 2#u8 := by
    simpa [countsAt] using
      (arrayMake4Index0 2#u8 0#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun, allSameFindExisting, coefficientRun,
    powerRun, coefficient2Run, countRun, u8TwoSucc]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficientsAt, countsAt, slots0, Array.update, Std.lift]
  constructor <;> apply Subtype.ext <;> rfl

private theorem allSameOuterStep3
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient2 coefficient3 : RawQM31)
    (coefficient3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          coefficient2 alpha = ok coefficient3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 3#usize) (unique1 group) (coefficientsAt coefficient2)
        (countsAt 3#u8) slots0 1#usize =
      ok (cont (rangeFrom 4#usize, unique1 group,
        coefficientsAt coefficient3, countsAt 4#u8, slots0, 1#usize)) := by
  have groupRun : Array.index_usize (groupsAllSame group) 3#usize =
      ok group := by
    simpa [groupsAllSame] using
      (arrayMake4Index3 group group group group)
  have coefficientRun :
      Array.index_usize (coefficientsAt coefficient2) 0#usize =
        ok coefficient2 := by
    simpa [coefficientsAt] using
      (arrayMake4Index0 coefficient2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize (countsAt 3#u8) 0#usize = ok 3#u8 := by
    simpa [countsAt] using
      (arrayMake4Index0 3#u8 0#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun, allSameFindExisting, coefficientRun,
    powerRun, coefficient3Run, countRun, u8ThreeSucc]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficientsAt, countsAt, slots0, Array.update, Std.lift]
  constructor <;> apply Subtype.ext <;> rfl

private theorem allSameInnerStep
    (group : Std.U8) (groupValues : Slice RawQM31)
    (coefficient3 value contribution folded : RawQM31)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group) = ok value)
    (contributionRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value coefficient3 = ok contribution)
    (foldedRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution =
        ok folded) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (unique1 group) (coefficientsAt coefficient3)
        (countsAt 4#u8) slots0
        { start := 0#usize, «end» := 1#usize }
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 1#usize }, folded)) := by
  have uniqueRun : Array.index_usize (unique1 group) 0#usize = ok group := by
    simpa [unique1] using (arrayMake4Index0 group 0#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (coefficientsAt coefficient3) 0#usize =
        ok coefficient3 := by
    simpa [coefficientsAt] using
      (arrayMake4Index0 coefficient3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have countRun : Array.index_usize (countsAt 4#u8) 0#usize = ok 4#u8 := by
    simpa [countsAt] using
      (arrayMake4Index0 4#u8 0#u8 0#u8 0#u8)
  have firstSlotRun : Array.index_usize slots0 0#usize = ok 0#u8 := by
    have run := arrayIndexRun slots0 0#usize (by decide)
    have valueExact : slots0.val[0]! = 0#u8 := by
      change (List.replicate 4 0#u8)[0]! = 0#u8
      rfl
    change Array.index_usize slots0 0#usize = ok (slots0.val[0]!) at run
    rw [valueExact] at run
    exact run
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext0End1, uniqueRun, fromU8ToUsizeExact, valueRun, firstSlotRun,
    countRun, coefficientRun, contributionRun, foldedRun, Std.lift]

private theorem allSameInnerDone
    (group : Std.U8) (groupValues : Slice RawQM31)
    (coefficient3 folded : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (unique1 group) (coefficientsAt coefficient3)
        (countsAt 4#u8) slots0
        { start := 1#usize, «end» := 1#usize } folded =
      ok (done folded) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeDone1]

private theorem allSameInnerExact
    (group : Std.U8) (groupValues : Slice RawQM31)
    (coefficient3 value contribution folded : RawQM31)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group) = ok value)
    (contributionRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value coefficient3 = ok contribution)
    (foldedRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution =
        ok folded) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 1#usize }
        groupValues (unique1 group) (coefficientsAt coefficient3)
        (countsAt 4#u8) slots0
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO = ok folded := by
  have step := allSameInnerStep group groupValues coefficient3 value
    contribution folded valueRun contributionRun foldedRun
  have done := allSameInnerDone group groupValues coefficient3 folded
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
  rw [loop.eq_1]
  dsimp only
  rw [step]
  simp only
  rw [loop.eq_1]
  dsimp only
  rw [done]

private theorem allSameOuterDone
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient3 value contribution folded half1 out :
      RawQM31)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group) = ok value)
    (contributionRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value coefficient3 = ok contribution)
    (foldedRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution =
        ok folded)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half folded = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllSame group) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 4#usize) (unique1 group) (coefficientsAt coefficient3)
        (countsAt 4#u8) slots0 1#usize = ok (done out) := by
  have innerRun := allSameInnerExact group groupValues coefficient3 value
    contribution folded valueRun contributionRun foldedRun
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeDone4, innerRun, half1Run, outRun]

private theorem allSameOuterExact
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient1 coefficient2 coefficient3 value
      contribution folded half1 out : RawQM31)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient1)
    (coefficient2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          coefficient1 alpha2 = ok coefficient2)
    (coefficient3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          coefficient2 alpha = ok coefficient3)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group) = ok value)
    (contributionRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value coefficient3 = ok contribution)
    (foldedRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution =
        ok folded)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half folded = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
        (rangeFrom 0#usize) (groupsAllSame group) groupValues
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0
        slots0 0#usize = ok out := by
  have step0 := allSameOuterStep0 group groupValues alpha alpha2 alpha3
  have step1 := allSameOuterStep1 group groupValues alpha alpha2 alpha3
    coefficient1 coefficient1Run
  have step2 := allSameOuterStep2 group groupValues alpha alpha2 alpha3
    coefficient1 coefficient2 coefficient2Run
  have step3 := allSameOuterStep3 group groupValues alpha alpha2 alpha3
    coefficient2 coefficient3 coefficient3Run
  have done := allSameOuterDone group groupValues alpha alpha2 alpha3
    coefficient3 value contribution folded half1 out valueRun contributionRun
    foldedRun half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
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

theorem allSameSourceExact
    (group : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient1 coefficient2 coefficient3 value
      contribution folded half1 out : RawQM31)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient1)
    (coefficient2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          coefficient1 alpha2 = ok coefficient2)
    (coefficient3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          coefficient2 alpha = ok coefficient3)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group) = ok value)
    (contributionRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value coefficient3 = ok contribution)
    (foldedRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution =
        ok folded)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half folded = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (groupsAllSame group) groupValues alpha alpha2 alpha3 = ok out := by
  have run := allSameOuterExact group groupValues alpha alpha2 alpha3
    coefficient1 coefficient2 coefficient3 value contribution folded half1 out
    coefficient1Run coefficient2Run coefficient3Run valueRun contributionRun
    foldedRun half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  simpa [rangeFrom, powers, unique0, coefficients0, slots0] using run

/-- The duplicate-row optimization is only an implementation shortcut.  Its
result is still the same four-term dual fold as evaluating all four rows
separately. -/
theorem allSameProgramCorresponds
    (group : Std.U8) (groupValues : Slice RawQM31)
    (value alpha alpha2 alpha3 : RawQM31)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group) = ok value)
    (hvalue : CanonicalQM31 value)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      allSameProgram group groupValues alpha alpha2 alpha3 = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha) (fun _ => toMaintainedExact value) := by
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical,
      coefficient1Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
      oneCanonical halpha3
  obtain ⟨coefficient2, coefficient2Run, coefficient2Canonical,
      coefficient2Exact⟩ :=
    generated_qm31_add_corresponds coefficient1 alpha2
      coefficient1Canonical halpha2
  obtain ⟨coefficient3, coefficient3Run, coefficient3Canonical,
      coefficient3Exact⟩ :=
    generated_qm31_add_corresponds coefficient2 alpha
      coefficient2Canonical halpha
  obtain ⟨contribution, contributionRun, contributionCanonical,
      contributionExact⟩ :=
    generated_qm31_mul_corresponds value coefficient3 hvalue
      coefficient3Canonical
  obtain ⟨folded, foldedRun, foldedCanonical, foldedExact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution
      zeroCanonical contributionCanonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds folded foldedCanonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  refine ⟨out, ?_, outCanonical, ?_⟩
  · simp [allSameProgram, coefficient1Run, coefficient2Run, coefficient3Run,
      valueRun, contributionRun, foldedRun, half1Run, outRun]
  · have coefficient1ExactM :=
      congrArg oldQm31ToMaintained coefficient1Exact
    have coefficient2ExactM :=
      congrArg oldQm31ToMaintained coefficient2Exact
    have coefficient3ExactM :=
      congrArg oldQm31ToMaintained coefficient3Exact
    have contributionExactM :=
      congrArg oldQm31ToMaintained contributionExact
    have foldedExactM := congrArg oldQm31ToMaintained foldedExact
    have half1ExactM := congrArg oldQm31ToMaintained half1Exact
    have outExactM := congrArg oldQm31ToMaintained outExact
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_mul] at coefficient1ExactM
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_mul] at coefficient2ExactM
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_mul] at coefficient3ExactM
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_mul] at contributionExactM
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_mul] at foldedExactM
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_mul] at half1ExactM
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_mul] at outExactM
    have oneExact :
        toMaintainedExact
            V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = 1 := by
      rw [V5RelationLinkedGenerated.aspis_core.field.QM31.ONE]
      rfl
    have zeroExact :
        toMaintainedExact
            V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO = 0 := by
      rw [V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]
      rfl
    have fourNonzero : (4 : ExactQM31) ≠ 0 := by decide
    apply (eq_div_iff fourNonzero).2
    simp
    calc
      toMaintainedExact out * 4 =
          (toMaintainedExact out + toMaintainedExact out) +
            (toMaintainedExact out + toMaintainedExact out) := by ring
      _ = toMaintainedExact half1 + toMaintainedExact half1 := by
        rw [outExactM]
      _ = toMaintainedExact folded := half1ExactM
      _ = toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
            toMaintainedExact contribution := foldedExactM
      _ = toMaintainedExact value * toMaintainedExact coefficient3 := by
        rw [zeroExact, contributionExactM]
        ring
      _ = toMaintainedExact value *
          (((1 : ExactQM31) + toMaintainedExact alpha ^ 3) +
            toMaintainedExact alpha ^ 2 + toMaintainedExact alpha) := by
        rw [coefficient3ExactM, coefficient2ExactM, coefficient1ExactM,
          oneExact, alpha2Exact, alpha3Exact]
      _ = toMaintainedExact value +
          toMaintainedExact alpha ^ 3 * toMaintainedExact value +
          toMaintainedExact alpha ^ 2 * toMaintainedExact value +
          toMaintainedExact alpha * toMaintainedExact value := by ring

/-- The theorem above describes the arithmetic.  This theorem additionally
follows the exact Charon/Aeneas translation of the production Rust loop. -/
theorem allSameSourceCorresponds
    (group : Std.U8) (groupValues : Slice RawQM31)
    (value alpha alpha2 alpha3 : RawQM31)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group) = ok value)
    (hvalue : CanonicalQM31 value)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (groupsAllSame group) groupValues alpha alpha2 alpha3 = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha) (fun _ => toMaintainedExact value) := by
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
      oneCanonical halpha3
  obtain ⟨coefficient2, coefficient2Run, coefficient2Canonical, _⟩ :=
    generated_qm31_add_corresponds coefficient1 alpha2
      coefficient1Canonical halpha2
  obtain ⟨coefficient3, coefficient3Run, coefficient3Canonical, _⟩ :=
    generated_qm31_add_corresponds coefficient2 alpha
      coefficient2Canonical halpha
  obtain ⟨contribution, contributionRun, contributionCanonical, _⟩ :=
    generated_qm31_mul_corresponds value coefficient3 hvalue
      coefficient3Canonical
  obtain ⟨folded, foldedRun, foldedCanonical, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution
      zeroCanonical contributionCanonical
  obtain ⟨half1, half1Run, half1Canonical, _⟩ :=
    generated_qm31_half_corresponds folded foldedCanonical
  obtain ⟨out, outRun, _, _⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := allSameSourceExact group groupValues alpha alpha2 alpha3
    coefficient1 coefficient2 coefficient3 value contribution folded half1 out
    coefficient1Run coefficient2Run coefficient3Run valueRun contributionRun
    foldedRun half1Run outRun
  have programRun : allSameProgram group groupValues alpha alpha2 alpha3 =
      ok out := by
    simp [allSameProgram, coefficient1Run, coefficient2Run, coefficient3Run,
      valueRun, contributionRun, foldedRun, half1Run, outRun]
  obtain ⟨programOut, programOutRun, programOutCanonical, programOutExact⟩ :=
    allSameProgramCorresponds group groupValues value alpha alpha2 alpha3
      valueRun hvalue halpha halpha2 halpha3 alpha2Exact alpha3Exact
  rw [programRun] at programOutRun
  have outEq : out = programOut := by
    injection programOutRun
  subst programOut
  exact ⟨out, sourceRun, programOutCanonical, programOutExact⟩

end AspisV5RelationLinkedGroupTuple
