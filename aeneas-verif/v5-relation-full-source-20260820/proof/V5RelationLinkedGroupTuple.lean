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

/-! ## The released `[0, 0, 1, 1]` tuple -/

def groupsPairPair : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 0#u8, 1#u8, 1#u8]

private def pairUnique2 : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 0#u8, 0#u8]

private def pairCoefficients2
    (coefficient0 alpha2 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0, alpha2,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def pairCoefficientsFinal
    (coefficient0 coefficient1 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0, coefficient1,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def pairCounts21 : Array Std.U8 4#usize :=
  Array.make 4#usize [2#u8, 1#u8, 0#u8, 0#u8]

private def pairCounts22 : Array Std.U8 4#usize :=
  Array.make 4#usize [2#u8, 2#u8, 0#u8, 0#u8]

private def pairFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 2#u8, 0#u8, 0#u8]

private theorem rangeNext0End2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 2#usize } =
      ok (some 0#usize, { start := 1#usize, «end» := 2#usize }) := by
  have hmax : 0 < UScalar.max .Usize := by
    have h := (1#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext1End2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 2#usize } =
      ok (some 1#usize, { start := 2#usize, «end» := 2#usize }) := by
  have hmax : 1 < UScalar.max .Usize := by
    have h := (2#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeDone2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := 2#usize } =
      ok (none, { start := 2#usize, «end» := 2#usize }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

private theorem pairFindNewStep0 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (unique1 0#u8) 1#usize 1#u8 0#usize = ok (cont 1#usize) := by
  have indexRun : Array.index_usize (unique1 0#u8) 0#usize = ok 0#u8 := by
    simpa [unique1] using
      (arrayMake4Index0 0#u8 0#u8 0#u8 0#u8)
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, usizeZeroSucc, Std.lift]

private theorem pairFindNewDone :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (unique1 0#u8) 1#usize 1#u8 1#usize = ok (done 1#usize) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body]

private theorem pairFindNewGroup :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (unique1 0#u8) 1#usize 1#u8 0#usize = ok 1#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  rw [pairFindNewStep0]
  simp only
  rw [loop.eq_1]
  rw [pairFindNewDone]

private theorem pairFindSecondStep0 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        pairUnique2 2#usize 1#u8 0#usize = ok (cont 1#usize) := by
  have indexRun : Array.index_usize pairUnique2 0#usize = ok 0#u8 := by
    simpa [pairUnique2] using
      (arrayMake4Index0 0#u8 1#u8 0#u8 0#u8)
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, usizeZeroSucc, Std.lift]

private theorem pairFindSecondDone :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        pairUnique2 2#usize 1#u8 1#usize = ok (done 1#usize) := by
  have indexRun : Array.index_usize pairUnique2 1#usize = ok 1#u8 := by
    simpa [pairUnique2] using
      (arrayMake4Index1 0#u8 1#u8 0#u8 0#u8)
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun]

private theorem pairFindSecondGroup :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        pairUnique2 2#usize 1#u8 0#usize = ok 1#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  rw [pairFindSecondStep0]
  simp only
  rw [loop.eq_1]
  rw [pairFindSecondDone]

private theorem usizeOneSucc :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#usize).hSize; scalar_tac)]
  norm_num

private theorem castUsizeTwoU8 :
    UScalar.cast .U8 2#usize = 2#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl

private theorem usizeTwoSucc :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#usize).hSize; scalar_tac)]
  norm_num

private theorem castUsizeOneU8 :
    UScalar.cast .U8 1#usize = 1#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl

private theorem pairOuterStep0
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsPairPair groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 0#usize) unique0 coefficients0 unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 0#u8, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeNext0, allSameFindEmpty, groupsPairPair, powers, rangeFrom, unique0,
    unique1, coefficients0, coefficients1, countsAt, slots0,
    Array.index_usize, Array.update, UScalar.lt_equiv, Std.lift]
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

private theorem pairOuterStep1
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsPairPair groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 1#usize) (unique1 0#u8) coefficients1 (countsAt 1#u8)
        slots0 1#usize =
      ok (cont (rangeFrom 2#usize, unique1 0#u8,
        coefficientsAt coefficient0, countsAt 2#u8, slots0, 1#usize)) := by
  have groupRun : Array.index_usize groupsPairPair 1#usize = ok 0#u8 := by
    simpa [groupsPairPair] using
      (arrayMake4Index1 0#u8 0#u8 1#u8 1#u8)
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
    simpa [countsAt] using (arrayMake4Index0 1#u8 0#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun, allSameFindExisting, coefficientRun,
    powerRun, coefficient0Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, coefficientsAt, countsAt, slots0,
    Array.update, Std.lift]
  constructor <;> apply Subtype.ext <;> rfl

private theorem pairOuterStep2
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsPairPair groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 2#usize) (unique1 0#u8) (coefficientsAt coefficient0)
        (countsAt 2#u8) slots0 1#usize =
      ok (cont (rangeFrom 3#usize, pairUnique2,
        pairCoefficients2 coefficient0 alpha2, pairCounts21, pairFirstSlots,
        2#usize)) := by
  have groupRun : Array.index_usize groupsPairPair 2#usize = ok 1#u8 := by
    simpa [groupsPairPair] using
      (arrayMake4Index2 0#u8 0#u8 1#u8 1#u8)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun, pairFindNewGroup, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficientsAt, countsAt, slots0, pairUnique2,
    pairCoefficients2, pairCounts21, pairFirstSlots, Array.update,
    Std.lift, castUsizeTwoU8, usizeOneSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem pairOuterStep3
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 : RawQM31)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha2 alpha =
        ok coefficient1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsPairPair groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 3#usize) pairUnique2
        (pairCoefficients2 coefficient0 alpha2) pairCounts21 pairFirstSlots
        2#usize =
      ok (cont (rangeFrom 4#usize, pairUnique2,
        pairCoefficientsFinal coefficient0 coefficient1, pairCounts22,
        pairFirstSlots, 2#usize)) := by
  have groupRun : Array.index_usize groupsPairPair 3#usize = ok 1#u8 := by
    simpa [groupsPairPair] using
      (arrayMake4Index3 0#u8 0#u8 1#u8 1#u8)
  have coefficientRun :
      Array.index_usize (pairCoefficients2 coefficient0 alpha2) 1#usize =
        ok alpha2 := by
    simpa [pairCoefficients2] using
      (arrayMake4Index1 coefficient0 alpha2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize pairCounts21 1#usize = ok 1#u8 := by
    simpa [pairCounts21] using
      (arrayMake4Index1 2#u8 1#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun, pairFindSecondGroup, coefficientRun,
    powerRun, coefficient1Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [pairUnique2, pairCoefficients2, pairCoefficientsFinal, pairCounts21,
    pairCounts22, pairFirstSlots, Array.update, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem pairInnerStep0
    (groupValues : Slice RawQM31)
    (coefficient0 coefficient1 value0 contribution0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues pairUnique2
        (pairCoefficientsFinal coefficient0 coefficient1) pairCounts22
        pairFirstSlots { start := 0#usize, «end» := 2#usize }
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 2#usize }, sum0)) := by
  have uniqueRun : Array.index_usize pairUnique2 0#usize = ok 0#u8 := by
    simpa [pairUnique2] using
      (arrayMake4Index0 0#u8 1#u8 0#u8 0#u8)
  have firstSlotRun : Array.index_usize pairFirstSlots 0#usize = ok 0#u8 := by
    simpa [pairFirstSlots] using
      (arrayMake4Index0 0#u8 2#u8 0#u8 0#u8)
  have countRun : Array.index_usize pairCounts22 0#usize = ok 2#u8 := by
    simpa [pairCounts22] using
      (arrayMake4Index0 2#u8 2#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (pairCoefficientsFinal coefficient0 coefficient1)
          0#usize = ok coefficient0 := by
    simpa [pairCoefficientsFinal] using
      (arrayMake4Index0 coefficient0 coefficient1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext0End2, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, coefficientRun, contribution0Run, sum0Run, Std.lift]

private theorem pairInnerStep1
    (groupValues : Slice RawQM31)
    (coefficient0 coefficient1 value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues pairUnique2
        (pairCoefficientsFinal coefficient0 coefficient1) pairCounts22
        pairFirstSlots { start := 1#usize, «end» := 2#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 2#usize }, sum1)) := by
  have uniqueRun : Array.index_usize pairUnique2 1#usize = ok 1#u8 := by
    simpa [pairUnique2] using
      (arrayMake4Index1 0#u8 1#u8 0#u8 0#u8)
  have firstSlotRun : Array.index_usize pairFirstSlots 1#usize = ok 2#u8 := by
    simpa [pairFirstSlots] using
      (arrayMake4Index1 0#u8 2#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (pairCoefficientsFinal coefficient0 coefficient1)
          1#usize = ok coefficient1 := by
    simpa [pairCoefficientsFinal] using
      (arrayMake4Index1 coefficient0 coefficient1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext1End2, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem pairInnerDone
    (groupValues : Slice RawQM31)
    (coefficient0 coefficient1 sum1 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues pairUnique2
        (pairCoefficientsFinal coefficient0 coefficient1) pairCounts22
        pairFirstSlots { start := 2#usize, «end» := 2#usize } sum1 =
      ok (done sum1) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeDone2]

private theorem pairInnerExact
    (groupValues : Slice RawQM31)
    (coefficient0 coefficient1 value0 value1 contribution0 contribution1
      sum0 sum1 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 2#usize } groupValues pairUnique2
        (pairCoefficientsFinal coefficient0 coefficient1) pairCounts22
        pairFirstSlots V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok sum1 := by
  have step0 := pairInnerStep0 groupValues coefficient0 coefficient1 value0
    contribution0 sum0 value0Run contribution0Run sum0Run
  have step1 := pairInnerStep1 groupValues coefficient0 coefficient1 value1
    contribution1 sum0 sum1 value1Run contribution1Run sum1Run
  have done := pairInnerDone groupValues coefficient0 coefficient1 sum1
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
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
  rw [done]

private theorem pairOuterDone
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1
      contribution0 contribution1 sum0 sum1 half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsPairPair groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 4#usize) pairUnique2
        (pairCoefficientsFinal coefficient0 coefficient1) pairCounts22
        pairFirstSlots 2#usize = ok (done out) := by
  have innerRun := pairInnerExact groupValues coefficient0 coefficient1
    value0 value1 contribution0 contribution1 sum0 sum1 value0Run value1Run
    contribution0Run contribution1Run sum0Run sum1Run
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeDone4, innerRun, half1Run, outRun]

private theorem pairOuterExact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1
      contribution0 contribution1 sum0 sum1 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient0)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha2 alpha =
        ok coefficient1)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
        (rangeFrom 0#usize) groupsPairPair groupValues
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0 slots0
        0#usize = ok out := by
  have step0 := pairOuterStep0 groupValues alpha alpha2 alpha3
  have step1 := pairOuterStep1 groupValues alpha alpha2 alpha3 coefficient0
    coefficient0Run
  have step2 := pairOuterStep2 groupValues alpha alpha2 alpha3 coefficient0
  have step3 := pairOuterStep3 groupValues alpha alpha2 alpha3 coefficient0
    coefficient1 coefficient1Run
  have done := pairOuterDone groupValues alpha alpha2 alpha3 coefficient0
    coefficient1 value0 value1 contribution0 contribution1 sum0 sum1 half1 out
    value0Run value1Run contribution0Run contribution1Run sum0Run sum1Run
    half1Run outRun
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

theorem pairPairSourceExact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1
      contribution0 contribution1 sum0 sum1 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient0)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha2 alpha =
        ok coefficient1)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        groupsPairPair groupValues alpha alpha2 alpha3 = ok out := by
  have run := pairOuterExact groupValues alpha alpha2 alpha3 coefficient0
    coefficient1 value0 value1 contribution0 contribution1 sum0 sum1 half1 out
    coefficient0Run coefficient1Run value0Run value1Run contribution0Run
    contribution1Run sum0Run sum1Run half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  simpa [rangeFrom, powers, unique0, coefficients0, slots0] using run

theorem pairPairSourceCorresponds
    (groupValues : Slice RawQM31)
    (value0 value1 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 0#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value1)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          groupsPairPair groupValues alpha alpha2 alpha3 = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value0,
            toMaintainedExact value1, toMaintainedExact value1] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
      oneCanonical alpha3Canonical
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical,
      coefficient1Exact⟩ :=
    generated_qm31_add_corresponds alpha2 alpha alpha2Canonical alphaCanonical
  obtain ⟨contribution0, contribution0Run, contribution0Canonical,
      contribution0Exact⟩ :=
    generated_qm31_mul_corresponds value0 coefficient0 value0Canonical
      coefficient0Canonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 coefficient1 value1Canonical
      coefficient1Canonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0
      zeroCanonical contribution0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum1 sum1Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := pairPairSourceExact groupValues alpha alpha2 alpha3
    coefficient0 coefficient1 value0 value1 contribution0 contribution1
    sum0 sum1 half1 out coefficient0Run coefficient1Run value0Run value1Run
    contribution0Run contribution1Run sum0Run sum1Run half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient0ExactM := congrArg oldQm31ToMaintained coefficient0Exact
  have coefficient1ExactM := congrArg oldQm31ToMaintained coefficient1Exact
  have contribution0ExactM := congrArg oldQm31ToMaintained contribution0Exact
  have contribution1ExactM := congrArg oldQm31ToMaintained contribution1Exact
  have sum0ExactM := congrArg oldQm31ToMaintained sum0Exact
  have sum1ExactM := congrArg oldQm31ToMaintained sum1Exact
  have half1ExactM := congrArg oldQm31ToMaintained half1Exact
  have outExactM := congrArg oldQm31ToMaintained outExact
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at half1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at outExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution1ExactM
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
    _ = toMaintainedExact sum1 := half1ExactM
    _ = toMaintainedExact sum0 + toMaintainedExact contribution1 := sum1ExactM
    _ = (toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
          toMaintainedExact contribution0) +
        toMaintainedExact contribution1 := by rw [sum0ExactM]
    _ = toMaintainedExact value0 * toMaintainedExact coefficient0 +
        toMaintainedExact value1 * toMaintainedExact coefficient1 := by
      rw [zeroExact, contribution0ExactM, contribution1ExactM]
      ring
    _ = toMaintainedExact value0 *
          ((1 : ExactQM31) + toMaintainedExact alpha ^ 3) +
        toMaintainedExact value1 *
          (toMaintainedExact alpha ^ 2 + toMaintainedExact alpha) := by
      rw [coefficient0ExactM, coefficient1ExactM, oneExact, alpha2Exact,
        alpha3Exact]
    _ = toMaintainedExact value0 +
        toMaintainedExact alpha ^ 3 * toMaintainedExact value0 +
        toMaintainedExact alpha ^ 2 * toMaintainedExact value1 +
        toMaintainedExact alpha * toMaintainedExact value1 := by ring

/-! ## The released `[1, 1, 1, 2]` tuple -/

def groupsTripleFirst : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 1#u8, 2#u8]

private def tripleUnique2 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 2#u8, 0#u8, 0#u8]

private def tripleCoefficientsFinal
    (coefficient0 : RawQM31) (alpha : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0, alpha,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def tripleCounts31 : Array Std.U8 4#usize :=
  Array.make 4#usize [3#u8, 1#u8, 0#u8, 0#u8]

private def tripleFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 3#u8, 0#u8, 0#u8]

private theorem tripleFindNewStep0 :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (unique1 1#u8) 1#usize 2#u8 0#usize = ok (cont 1#usize) := by
  have indexRun : Array.index_usize (unique1 1#u8) 0#usize = ok 1#u8 := by
    simpa [unique1] using
      (arrayMake4Index0 1#u8 0#u8 0#u8 0#u8)
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, usizeZeroSucc, Std.lift]

private theorem tripleFindNewDone :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (unique1 1#u8) 1#usize 2#u8 1#usize = ok (done 1#usize) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body]

private theorem tripleFindNewGroup :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (unique1 1#u8) 1#usize 2#u8 0#usize = ok 1#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  rw [tripleFindNewStep0]
  simp only
  rw [loop.eq_1]
  rw [tripleFindNewDone]

private theorem castUsizeThreeU8 :
    UScalar.cast .U8 3#usize = 3#u8 := by
  apply UScalar.val_eq_imp
  rw [UScalar.cast_val_eq]
  rfl

private theorem tripleOuterStep0
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsTripleFirst groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 0#usize) unique0 coefficients0 unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 1#u8, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeNext0, allSameFindEmpty, groupsTripleFirst, powers, rangeFrom, unique0,
    unique1, coefficients0, coefficients1, countsAt, slots0,
    Array.index_usize, Array.update, UScalar.lt_equiv, Std.lift]
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

private theorem tripleOuterStep1
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsTripleFirst groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 1#usize) (unique1 1#u8) coefficients1 (countsAt 1#u8)
        slots0 1#usize =
      ok (cont (rangeFrom 2#usize, unique1 1#u8,
        coefficientsAt coefficient0, countsAt 2#u8, slots0, 1#usize)) := by
  have groupRun : Array.index_usize groupsTripleFirst 1#usize = ok 1#u8 := by
    simpa [groupsTripleFirst] using
      (arrayMake4Index1 1#u8 1#u8 1#u8 2#u8)
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
    simpa [countsAt] using (arrayMake4Index0 1#u8 0#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun, allSameFindExisting, coefficientRun,
    powerRun, coefficient0Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, coefficientsAt, countsAt, slots0,
    Array.update, Std.lift]
  constructor <;> apply Subtype.ext <;> rfl

private theorem tripleOuterStep2
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 : RawQM31)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          coefficient0 alpha2 = ok coefficient1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsTripleFirst groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 2#usize) (unique1 1#u8) (coefficientsAt coefficient0)
        (countsAt 2#u8) slots0 1#usize =
      ok (cont (rangeFrom 3#usize, unique1 1#u8,
        coefficientsAt coefficient1, countsAt 3#u8, slots0, 1#usize)) := by
  have groupRun : Array.index_usize groupsTripleFirst 2#usize = ok 1#u8 := by
    simpa [groupsTripleFirst] using
      (arrayMake4Index2 1#u8 1#u8 1#u8 2#u8)
  have coefficientRun :
      Array.index_usize (coefficientsAt coefficient0) 0#usize =
        ok coefficient0 := by
    simpa [coefficientsAt] using
      (arrayMake4Index0 coefficient0
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
    simpa [countsAt] using (arrayMake4Index0 2#u8 0#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun, allSameFindExisting, coefficientRun,
    powerRun, coefficient1Run, countRun, u8TwoSucc]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficientsAt, countsAt, slots0, Array.update, Std.lift]
  constructor <;> apply Subtype.ext <;> rfl

private theorem tripleOuterStep3
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient1 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsTripleFirst groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 3#usize) (unique1 1#u8) (coefficientsAt coefficient1)
        (countsAt 3#u8) slots0 1#usize =
      ok (cont (rangeFrom 4#usize, tripleUnique2,
        tripleCoefficientsFinal coefficient1 alpha, tripleCounts31,
        tripleFirstSlots, 2#usize)) := by
  have groupRun : Array.index_usize groupsTripleFirst 3#usize = ok 2#u8 := by
    simpa [groupsTripleFirst] using
      (arrayMake4Index3 1#u8 1#u8 1#u8 2#u8)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun, tripleFindNewGroup, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficientsAt, countsAt, slots0, tripleUnique2,
    tripleCoefficientsFinal, tripleCounts31, tripleFirstSlots, Array.update,
    Std.lift, castUsizeThreeU8, usizeOneSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem tripleInnerStep0
    (groupValues : Slice RawQM31)
    (coefficient0 alpha value0 contribution0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value0)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues tripleUnique2 (tripleCoefficientsFinal coefficient0 alpha)
        tripleCounts31 tripleFirstSlots
        { start := 0#usize, «end» := 2#usize }
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 2#usize }, sum0)) := by
  have uniqueRun : Array.index_usize tripleUnique2 0#usize = ok 1#u8 := by
    simpa [tripleUnique2] using
      (arrayMake4Index0 1#u8 2#u8 0#u8 0#u8)
  have firstSlotRun :
      Array.index_usize tripleFirstSlots 0#usize = ok 0#u8 := by
    simpa [tripleFirstSlots] using
      (arrayMake4Index0 0#u8 3#u8 0#u8 0#u8)
  have countRun : Array.index_usize tripleCounts31 0#usize = ok 3#u8 := by
    simpa [tripleCounts31] using
      (arrayMake4Index0 3#u8 1#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (tripleCoefficientsFinal coefficient0 alpha)
          0#usize = ok coefficient0 := by
    simpa [tripleCoefficientsFinal] using
      (arrayMake4Index0 coefficient0 alpha
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext0End2, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, coefficientRun, contribution0Run, sum0Run, Std.lift]

private theorem tripleInnerStep1
    (groupValues : Slice RawQM31)
    (coefficient0 alpha value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 2#u8) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul value1 alpha =
        ok contribution1)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues tripleUnique2 (tripleCoefficientsFinal coefficient0 alpha)
        tripleCounts31 tripleFirstSlots
        { start := 1#usize, «end» := 2#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 2#usize }, sum1)) := by
  have uniqueRun : Array.index_usize tripleUnique2 1#usize = ok 2#u8 := by
    simpa [tripleUnique2] using
      (arrayMake4Index1 1#u8 2#u8 0#u8 0#u8)
  have firstSlotRun :
      Array.index_usize tripleFirstSlots 1#usize = ok 3#u8 := by
    simpa [tripleFirstSlots] using
      (arrayMake4Index1 0#u8 3#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (tripleCoefficientsFinal coefficient0 alpha)
          1#usize = ok alpha := by
    simpa [tripleCoefficientsFinal] using
      (arrayMake4Index1 coefficient0 alpha
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext1End2, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem tripleInnerDone
    (groupValues : Slice RawQM31) (coefficient0 alpha sum1 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues tripleUnique2 (tripleCoefficientsFinal coefficient0 alpha)
        tripleCounts31 tripleFirstSlots
        { start := 2#usize, «end» := 2#usize } sum1 = ok (done sum1) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeDone2]

private theorem tripleInnerExact
    (groupValues : Slice RawQM31)
    (coefficient0 alpha value0 value1 contribution0 contribution1 sum0 sum1 :
      RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 2#u8) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul value1 alpha =
        ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 2#usize } groupValues tripleUnique2
        (tripleCoefficientsFinal coefficient0 alpha) tripleCounts31
        tripleFirstSlots V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok sum1 := by
  have step0 := tripleInnerStep0 groupValues coefficient0 alpha value0
    contribution0 sum0 value0Run contribution0Run sum0Run
  have step1 := tripleInnerStep1 groupValues coefficient0 alpha value1
    contribution1 sum0 sum1 value1Run contribution1Run sum1Run
  have done := tripleInnerDone groupValues coefficient0 alpha sum1
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
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
  rw [done]

private theorem tripleOuterDone
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 value0 value1 contribution0 contribution1
      sum0 sum1 half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 2#u8) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul value1 alpha =
        ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        groupsTripleFirst groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 4#usize) tripleUnique2
        (tripleCoefficientsFinal coefficient0 alpha) tripleCounts31
        tripleFirstSlots 2#usize = ok (done out) := by
  have innerRun := tripleInnerExact groupValues coefficient0 alpha value0
    value1 contribution0 contribution1 sum0 sum1 value0Run value1Run
    contribution0Run contribution1Run sum0Run sum1Run
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeDone4, innerRun, half1Run, outRun]

private theorem tripleOuterExact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1 contribution0
      contribution1 sum0 sum1 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient0)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          coefficient0 alpha2 = ok coefficient1)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 2#u8) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient1 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul value1 alpha =
        ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
        (rangeFrom 0#usize) groupsTripleFirst groupValues
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0 slots0
        0#usize = ok out := by
  have step0 := tripleOuterStep0 groupValues alpha alpha2 alpha3
  have step1 := tripleOuterStep1 groupValues alpha alpha2 alpha3 coefficient0
    coefficient0Run
  have step2 := tripleOuterStep2 groupValues alpha alpha2 alpha3 coefficient0
    coefficient1 coefficient1Run
  have step3 := tripleOuterStep3 groupValues alpha alpha2 alpha3 coefficient1
  have done := tripleOuterDone groupValues alpha alpha2 alpha3 coefficient1
    value0 value1 contribution0 contribution1 sum0 sum1 half1 out value0Run
    value1Run contribution0Run contribution1Run sum0Run sum1Run half1Run outRun
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

theorem tripleFirstSourceExact
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1 contribution0
      contribution1 sum0 sum1 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient0)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          coefficient0 alpha2 = ok coefficient1)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 2#u8) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient1 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul value1 alpha =
        ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        groupsTripleFirst groupValues alpha alpha2 alpha3 = ok out := by
  have run := tripleOuterExact groupValues alpha alpha2 alpha3 coefficient0
    coefficient1 value0 value1 contribution0 contribution1 sum0 sum1 half1 out
    coefficient0Run coefficient1Run value0Run value1Run contribution0Run
    contribution1Run sum0Run sum1Run half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  simpa [rangeFrom, powers, unique0, coefficients0, slots0] using run

theorem tripleFirstSourceCorresponds
    (groupValues : Slice RawQM31)
    (value0 value1 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 1#u8) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize 2#u8) = ok value1)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          groupsTripleFirst groupValues alpha alpha2 alpha3 = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value0,
            toMaintainedExact value0, toMaintainedExact value1] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
      oneCanonical alpha3Canonical
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical,
      coefficient1Exact⟩ :=
    generated_qm31_add_corresponds coefficient0 alpha2 coefficient0Canonical
      alpha2Canonical
  obtain ⟨contribution0, contribution0Run, contribution0Canonical,
      contribution0Exact⟩ :=
    generated_qm31_mul_corresponds value0 coefficient1 value0Canonical
      coefficient1Canonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha value1Canonical alphaCanonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0
      zeroCanonical contribution0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum1 sum1Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := tripleFirstSourceExact groupValues alpha alpha2 alpha3
    coefficient0 coefficient1 value0 value1 contribution0 contribution1
    sum0 sum1 half1 out coefficient0Run coefficient1Run value0Run value1Run
    contribution0Run contribution1Run sum0Run sum1Run half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient0ExactM := congrArg oldQm31ToMaintained coefficient0Exact
  have coefficient1ExactM := congrArg oldQm31ToMaintained coefficient1Exact
  have contribution0ExactM := congrArg oldQm31ToMaintained contribution0Exact
  have contribution1ExactM := congrArg oldQm31ToMaintained contribution1Exact
  have sum0ExactM := congrArg oldQm31ToMaintained sum0Exact
  have sum1ExactM := congrArg oldQm31ToMaintained sum1Exact
  have half1ExactM := congrArg oldQm31ToMaintained half1Exact
  have outExactM := congrArg oldQm31ToMaintained outExact
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at half1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at outExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution1ExactM
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
    _ = toMaintainedExact sum1 := half1ExactM
    _ = toMaintainedExact sum0 + toMaintainedExact contribution1 := sum1ExactM
    _ = (toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
          toMaintainedExact contribution0) +
        toMaintainedExact contribution1 := by rw [sum0ExactM]
    _ = toMaintainedExact value0 * toMaintainedExact coefficient1 +
        toMaintainedExact value1 * toMaintainedExact alpha := by
      rw [zeroExact, contribution0ExactM, contribution1ExactM]
      ring
    _ = toMaintainedExact value0 *
          (((1 : ExactQM31) + toMaintainedExact alpha ^ 3) +
            toMaintainedExact alpha ^ 2) +
        toMaintainedExact value1 * toMaintainedExact alpha := by
      rw [coefficient1ExactM, coefficient0ExactM, oneExact, alpha2Exact,
        alpha3Exact]
    _ = toMaintainedExact value0 +
        toMaintainedExact alpha ^ 3 * toMaintainedExact value0 +
        toMaintainedExact alpha ^ 2 * toMaintainedExact value0 +
        toMaintainedExact alpha * toMaintainedExact value1 := by ring

/-! ## The two released `[A, B, B, B]` tuples -/

def groupsOneThree (group0 group1 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group1, group1]

private def oneThreeUnique2
    (group0 group1 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, 0#u8, 0#u8]

private def oneThreeCoefficients1
    (alpha3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE, alpha3,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def oneThreeCoefficientsAt
    (coefficient : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE, coefficient,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def oneThreeCounts11 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 0#u8, 0#u8]

private def oneThreeCounts12 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 2#u8, 0#u8, 0#u8]

private def oneThreeCounts13 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 3#u8, 0#u8, 0#u8]

private def oneThreeFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 0#u8, 0#u8]

private theorem oneThreeFindNewStep0
    (group0 group1 : Std.U8) (different : group0 ≠ group1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (unique1 group0) 1#usize group1 0#usize = ok (cont 1#usize) := by
  have indexRun : Array.index_usize (unique1 group0) 0#usize = ok group0 := by
    simpa [unique1] using
      (arrayMake4Index0 group0 0#u8 0#u8 0#u8)
  have differentVal : group0.val ≠ group1.val := by
    intro same
    apply different
    apply UScalar.val_eq_imp
    exact same
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, differentVal, usizeZeroSucc, Std.lift]

private theorem oneThreeFindNewDone
    (group0 group1 : Std.U8) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (unique1 group0) 1#usize group1 1#usize = ok (done 1#usize) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body]

private theorem oneThreeFindNew
    (group0 group1 : Std.U8) (different : group0 ≠ group1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (unique1 group0) 1#usize group1 0#usize = ok 1#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  rw [oneThreeFindNewStep0 group0 group1 different]
  simp only
  rw [loop.eq_1]
  rw [oneThreeFindNewDone]

private theorem oneThreeFindExistingStep0
    (group0 group1 : Std.U8) (different : group0 ≠ group1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (oneThreeUnique2 group0 group1) 2#usize group1 0#usize =
      ok (cont 1#usize) := by
  have indexRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 0#usize =
        ok group0 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index0 group0 group1 0#u8 0#u8)
  have differentVal : group0.val ≠ group1.val := by
    intro same
    apply different
    apply UScalar.val_eq_imp
    exact same
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, differentVal, usizeZeroSucc, Std.lift]

private theorem oneThreeFindExistingDone
    (group0 group1 : Std.U8) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (oneThreeUnique2 group0 group1) 2#usize group1 1#usize =
      ok (done 1#usize) := by
  have indexRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 1#usize =
        ok group1 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index1 group0 group1 0#u8 0#u8)
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun]

private theorem oneThreeFindExisting
    (group0 group1 : Std.U8) (different : group0 ≠ group1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (oneThreeUnique2 group0 group1) 2#usize group1 0#usize = ok 1#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  rw [oneThreeFindExistingStep0 group0 group1 different]
  simp only
  rw [loop.eq_1]
  rw [oneThreeFindExistingDone]

private theorem oneThreeOuterStep0
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsOneThree group0 group1) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 0#usize) unique0 coefficients0 unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeNext0, allSameFindEmpty, groupsOneThree, powers, rangeFrom, unique0,
    unique1, coefficients0, coefficients1, countsAt, slots0,
    Array.index_usize, Array.update, UScalar.lt_equiv, Std.lift]
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

private theorem oneThreeOuterStep1
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsOneThree group0 group1) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 1#usize) (unique1 group0) coefficients1 (countsAt 1#u8)
        slots0 1#usize =
      ok (cont (rangeFrom 2#usize, oneThreeUnique2 group0 group1,
        oneThreeCoefficients1 alpha3, oneThreeCounts11, oneThreeFirstSlots,
        2#usize)) := by
  have groupRun :
      Array.index_usize (groupsOneThree group0 group1) 1#usize =
        ok group1 := by
    simpa [groupsOneThree] using
      (arrayMake4Index1 group0 group1 group1 group1)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 1#usize =
      ok alpha3 := by
    simpa [powers] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun,
    oneThreeFindNew group0 group1 different, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, countsAt, slots0, oneThreeUnique2,
    oneThreeCoefficients1, oneThreeCounts11, oneThreeFirstSlots,
    Array.update, Std.lift, castUsizeOneU8, usizeOneSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem oneThreeOuterStep2
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha3 alpha2 =
        ok coefficient0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsOneThree group0 group1) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 2#usize) (oneThreeUnique2 group0 group1)
        (oneThreeCoefficients1 alpha3) oneThreeCounts11 oneThreeFirstSlots
        2#usize =
      ok (cont (rangeFrom 3#usize, oneThreeUnique2 group0 group1,
        oneThreeCoefficientsAt coefficient0, oneThreeCounts12,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsOneThree group0 group1) 2#usize =
        ok group1 := by
    simpa [groupsOneThree] using
      (arrayMake4Index2 group0 group1 group1 group1)
  have coefficientRun :
      Array.index_usize (oneThreeCoefficients1 alpha3) 1#usize = ok alpha3 := by
    simpa [oneThreeCoefficients1] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize oneThreeCounts11 1#usize = ok 1#u8 := by
    simpa [oneThreeCounts11] using
      (arrayMake4Index1 1#u8 1#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun,
    oneThreeFindExisting group0 group1 different, coefficientRun, powerRun,
    coefficient0Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, oneThreeCoefficients1, oneThreeCoefficientsAt,
    oneThreeCounts11, oneThreeCounts12, oneThreeFirstSlots, Array.update,
    Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem oneThreeOuterStep3
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 : RawQM31)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add coefficient0 alpha =
        ok coefficient1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsOneThree group0 group1) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 3#usize) (oneThreeUnique2 group0 group1)
        (oneThreeCoefficientsAt coefficient0) oneThreeCounts12
        oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 4#usize, oneThreeUnique2 group0 group1,
        oneThreeCoefficientsAt coefficient1, oneThreeCounts13,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsOneThree group0 group1) 3#usize =
        ok group1 := by
    simpa [groupsOneThree] using
      (arrayMake4Index3 group0 group1 group1 group1)
  have coefficientRun :
      Array.index_usize (oneThreeCoefficientsAt coefficient0) 1#usize =
        ok coefficient0 := by
    simpa [oneThreeCoefficientsAt] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE coefficient0
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize oneThreeCounts12 1#usize = ok 2#u8 := by
    simpa [oneThreeCounts12] using
      (arrayMake4Index1 1#u8 2#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    oneThreeFindExisting group0 group1 different, coefficientRun, powerRun,
    coefficient1Run, countRun, u8TwoSucc]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, oneThreeCoefficientsAt, oneThreeCounts12,
    oneThreeCounts13, oneThreeFirstSlots, Array.update, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem oneThreeInnerStep0
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient value0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (oneThreeUnique2 group0 group1)
        (oneThreeCoefficientsAt coefficient) oneThreeCounts13
        oneThreeFirstSlots { start := 0#usize, «end» := 2#usize }
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 2#usize }, sum0)) := by
  have uniqueRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 0#usize =
        ok group0 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index0 group0 group1 0#u8 0#u8)
  have firstSlotRun :
      Array.index_usize oneThreeFirstSlots 0#usize = ok 0#u8 := by
    simpa [oneThreeFirstSlots] using
      (arrayMake4Index0 0#u8 1#u8 0#u8 0#u8)
  have countRun : Array.index_usize oneThreeCounts13 0#usize = ok 1#u8 := by
    simpa [oneThreeCounts13] using
      (arrayMake4Index0 1#u8 3#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext0End2, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, sum0Run, Std.lift]

private theorem oneThreeInnerStep1
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient = ok contribution1)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (oneThreeUnique2 group0 group1)
        (oneThreeCoefficientsAt coefficient) oneThreeCounts13
        oneThreeFirstSlots { start := 1#usize, «end» := 2#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 2#usize }, sum1)) := by
  have uniqueRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 1#usize =
        ok group1 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index1 group0 group1 0#u8 0#u8)
  have firstSlotRun :
      Array.index_usize oneThreeFirstSlots 1#usize = ok 1#u8 := by
    simpa [oneThreeFirstSlots] using
      (arrayMake4Index1 0#u8 1#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (oneThreeCoefficientsAt coefficient) 1#usize =
        ok coefficient := by
    simpa [oneThreeCoefficientsAt] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE coefficient
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext1End2, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem oneThreeInnerDone
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient sum1 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (oneThreeUnique2 group0 group1)
        (oneThreeCoefficientsAt coefficient) oneThreeCounts13
        oneThreeFirstSlots { start := 2#usize, «end» := 2#usize } sum1 =
      ok (done sum1) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeDone2]

private theorem oneThreeInnerExact
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient value0 value1 contribution1 sum0 sum1 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 2#usize } groupValues
        (oneThreeUnique2 group0 group1) (oneThreeCoefficientsAt coefficient)
        oneThreeCounts13 oneThreeFirstSlots
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO = ok sum1 := by
  have step0 := oneThreeInnerStep0 group0 group1 groupValues coefficient
    value0 sum0 value0Run sum0Run
  have step1 := oneThreeInnerStep1 group0 group1 groupValues coefficient
    value1 contribution1 sum0 sum1 value1Run contribution1Run sum1Run
  have done := oneThreeInnerDone group0 group1 groupValues coefficient sum1
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
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
  rw [done]

private theorem oneThreeOuterDone
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient value0 value1 contribution1 sum0 sum1
      half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsOneThree group0 group1) groupValues (powers alpha alpha2 alpha3)
        (rangeFrom 4#usize) (oneThreeUnique2 group0 group1)
        (oneThreeCoefficientsAt coefficient) oneThreeCounts13
        oneThreeFirstSlots 2#usize = ok (done out) := by
  have innerRun := oneThreeInnerExact group0 group1 groupValues coefficient
    value0 value1 contribution1 sum0 sum1 value0Run value1Run contribution1Run
    sum0Run sum1Run
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeDone4, innerRun, half1Run, outRun]

private theorem oneThreeOuterExact
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1 contribution1
      sum0 sum1 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha3 alpha2 =
        ok coefficient0)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add coefficient0 alpha =
        ok coefficient1)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
        (rangeFrom 0#usize) (groupsOneThree group0 group1) groupValues
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0 slots0
        0#usize = ok out := by
  have step0 := oneThreeOuterStep0 group0 group1 groupValues alpha alpha2 alpha3
  have step1 := oneThreeOuterStep1 group0 group1 different groupValues alpha
    alpha2 alpha3
  have step2 := oneThreeOuterStep2 group0 group1 different groupValues alpha
    alpha2 alpha3 coefficient0 coefficient0Run
  have step3 := oneThreeOuterStep3 group0 group1 different groupValues alpha
    alpha2 alpha3 coefficient0 coefficient1 coefficient1Run
  have done := oneThreeOuterDone group0 group1 groupValues alpha alpha2 alpha3
    coefficient1 value0 value1 contribution1 sum0 sum1 half1 out value0Run
    value1Run contribution1Run sum0Run sum1Run half1Run outRun
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

theorem oneThreeSourceExact
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1 contribution1
      sum0 sum1 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha3 alpha2 =
        ok coefficient0)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add coefficient0 alpha =
        ok coefficient1)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (groupsOneThree group0 group1) groupValues alpha alpha2 alpha3 =
      ok out := by
  have run := oneThreeOuterExact group0 group1 different groupValues alpha
    alpha2 alpha3 coefficient0 coefficient1 value0 value1 contribution1 sum0
    sum1 half1 out coefficient0Run coefficient1Run value0Run value1Run
    contribution1Run sum0Run sum1Run half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  simpa [rangeFrom, powers, unique0, coefficients0, slots0] using run

theorem oneThreeSourceCorresponds
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (value0 value1 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (groupsOneThree group0 group1) groupValues alpha alpha2 alpha3 =
        ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value1,
            toMaintainedExact value1, toMaintainedExact value1] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    generated_qm31_add_corresponds alpha3 alpha2 alpha3Canonical
      alpha2Canonical
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical,
      coefficient1Exact⟩ :=
    generated_qm31_add_corresponds coefficient0 alpha coefficient0Canonical
      alphaCanonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 coefficient1 value1Canonical
      coefficient1Canonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0
      zeroCanonical value0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum1 sum1Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := oneThreeSourceExact group0 group1 different groupValues
    alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1 contribution1
    sum0 sum1 half1 out coefficient0Run coefficient1Run value0Run value1Run
    contribution1Run sum0Run sum1Run half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient0ExactM := congrArg oldQm31ToMaintained coefficient0Exact
  have coefficient1ExactM := congrArg oldQm31ToMaintained coefficient1Exact
  have contribution1ExactM := congrArg oldQm31ToMaintained contribution1Exact
  have sum0ExactM := congrArg oldQm31ToMaintained sum0Exact
  have sum1ExactM := congrArg oldQm31ToMaintained sum1Exact
  have half1ExactM := congrArg oldQm31ToMaintained half1Exact
  have outExactM := congrArg oldQm31ToMaintained outExact
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at half1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at outExactM
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
    _ = toMaintainedExact sum1 := half1ExactM
    _ = toMaintainedExact sum0 + toMaintainedExact contribution1 := sum1ExactM
    _ = (toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
          toMaintainedExact value0) + toMaintainedExact contribution1 := by
      rw [sum0ExactM]
    _ = toMaintainedExact value0 +
        toMaintainedExact value1 * toMaintainedExact coefficient1 := by
      rw [zeroExact, contribution1ExactM]
      ring
    _ = toMaintainedExact value0 +
        toMaintainedExact value1 *
          ((toMaintainedExact alpha ^ 3 + toMaintainedExact alpha ^ 2) +
            toMaintainedExact alpha) := by
      rw [coefficient1ExactM, coefficient0ExactM, alpha2Exact, alpha3Exact]
    _ = toMaintainedExact value0 +
        toMaintainedExact alpha ^ 3 * toMaintainedExact value1 +
        toMaintainedExact alpha ^ 2 * toMaintainedExact value1 +
        toMaintainedExact alpha * toMaintainedExact value1 := by ring

/-! ## The released `[1, 2, 1, 1]` tuple -/

def groupsThreeAround (group0 group1 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group0, group0]

private def threeAroundCoefficients11
    (alpha3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE, alpha3,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def threeAroundCoefficientsAt
    (coefficient alpha3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient, alpha3,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def threeAroundCounts21 : Array Std.U8 4#usize :=
  Array.make 4#usize [2#u8, 1#u8, 0#u8, 0#u8]

private def threeAroundCounts31 : Array Std.U8 4#usize :=
  Array.make 4#usize [3#u8, 1#u8, 0#u8, 0#u8]

private theorem threeAroundFindFirstDone
    (group0 group1 : Std.U8) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (oneThreeUnique2 group0 group1) 2#usize group0 0#usize =
      ok (done 0#usize) := by
  have indexRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 0#usize =
        ok group0 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index0 group0 group1 0#u8 0#u8)
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun]

private theorem threeAroundFindFirst
    (group0 group1 : Std.U8) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (oneThreeUnique2 group0 group1) 2#usize group0 0#usize =
      ok 0#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  rw [threeAroundFindFirstDone]

private theorem threeAroundOuterStep0
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsThreeAround group0 group1) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 0#usize) unique0 coefficients0
        unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeNext0, allSameFindEmpty, groupsThreeAround, powers, rangeFrom, unique0,
    unique1, coefficients0, coefficients1, countsAt, slots0,
    Array.index_usize, Array.update, UScalar.lt_equiv, Std.lift]
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

private theorem threeAroundOuterStep1
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsThreeAround group0 group1) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 1#usize) (unique1 group0)
        coefficients1 (countsAt 1#u8) slots0 1#usize =
      ok (cont (rangeFrom 2#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficients11 alpha3, oneThreeCounts11,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsThreeAround group0 group1) 1#usize =
        ok group1 := by
    simpa [groupsThreeAround] using
      (arrayMake4Index1 group0 group1 group0 group0)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 1#usize =
      ok alpha3 := by
    simpa [powers] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun,
    oneThreeFindNew group0 group1 different, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, countsAt, slots0, oneThreeUnique2,
    threeAroundCoefficients11, oneThreeCounts11, oneThreeFirstSlots,
    Array.update, Std.lift, castUsizeOneU8, usizeOneSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem threeAroundOuterStep2
    (group0 group1 : Std.U8)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha2 =
        ok coefficient0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsThreeAround group0 group1) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 2#usize)
        (oneThreeUnique2 group0 group1) (threeAroundCoefficients11 alpha3)
        oneThreeCounts11 oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 3#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficientsAt coefficient0 alpha3, threeAroundCounts21,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsThreeAround group0 group1) 2#usize =
        ok group0 := by
    simpa [groupsThreeAround] using
      (arrayMake4Index2 group0 group1 group0 group0)
  have coefficientRun :
      Array.index_usize (threeAroundCoefficients11 alpha3) 0#usize =
        ok V5RelationLinkedGenerated.aspis_core.field.QM31.ONE := by
    simpa [threeAroundCoefficients11] using
      (arrayMake4Index0
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize oneThreeCounts11 0#usize = ok 1#u8 := by
    simpa [oneThreeCounts11] using
      (arrayMake4Index0 1#u8 1#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun,
    threeAroundFindFirst group0 group1, coefficientRun, powerRun,
    coefficient0Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficients11,
    threeAroundCoefficientsAt, oneThreeCounts11, threeAroundCounts21,
    oneThreeFirstSlots, Array.update, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem threeAroundOuterStep3
    (group0 group1 : Std.U8)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 : RawQM31)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add coefficient0 alpha =
        ok coefficient1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsThreeAround group0 group1) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 3#usize)
        (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts21
        oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 4#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficientsAt coefficient1 alpha3, threeAroundCounts31,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsThreeAround group0 group1) 3#usize =
        ok group0 := by
    simpa [groupsThreeAround] using
      (arrayMake4Index3 group0 group1 group0 group0)
  have coefficientRun :
      Array.index_usize (threeAroundCoefficientsAt coefficient0 alpha3)
          0#usize = ok coefficient0 := by
    simpa [threeAroundCoefficientsAt] using
      (arrayMake4Index0 coefficient0 alpha3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize threeAroundCounts21 0#usize = ok 2#u8 := by
    simpa [threeAroundCounts21] using
      (arrayMake4Index0 2#u8 1#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    threeAroundFindFirst group0 group1, coefficientRun, powerRun,
    coefficient1Run, countRun, u8TwoSucc]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficientsAt, threeAroundCounts21,
    threeAroundCounts31, oneThreeFirstSlots, Array.update, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem threeAroundInnerStep0
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 value0 contribution0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts31
        oneThreeFirstSlots { start := 0#usize, «end» := 2#usize }
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 2#usize }, sum0)) := by
  have uniqueRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 0#usize =
        ok group0 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index0 group0 group1 0#u8 0#u8)
  have firstSlotRun :
      Array.index_usize oneThreeFirstSlots 0#usize = ok 0#u8 := by
    simpa [oneThreeFirstSlots] using
      (arrayMake4Index0 0#u8 1#u8 0#u8 0#u8)
  have countRun : Array.index_usize threeAroundCounts31 0#usize = ok 3#u8 := by
    simpa [threeAroundCounts31] using
      (arrayMake4Index0 3#u8 1#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (threeAroundCoefficientsAt coefficient0 alpha3)
          0#usize = ok coefficient0 := by
    simpa [threeAroundCoefficientsAt] using
      (arrayMake4Index0 coefficient0 alpha3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext0End2, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, coefficientRun, contribution0Run, sum0Run, Std.lift]

private theorem threeAroundInnerStep1
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts31
        oneThreeFirstSlots { start := 1#usize, «end» := 2#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 2#usize }, sum1)) := by
  have uniqueRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 1#usize =
        ok group1 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index1 group0 group1 0#u8 0#u8)
  have firstSlotRun :
      Array.index_usize oneThreeFirstSlots 1#usize = ok 1#u8 := by
    simpa [oneThreeFirstSlots] using
      (arrayMake4Index1 0#u8 1#u8 0#u8 0#u8)
  have coefficientRun :
      Array.index_usize (threeAroundCoefficientsAt coefficient0 alpha3)
          1#usize = ok alpha3 := by
    simpa [threeAroundCoefficientsAt] using
      (arrayMake4Index1 coefficient0 alpha3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext1End2, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem threeAroundInnerDone
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 sum1 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts31
        oneThreeFirstSlots { start := 2#usize, «end» := 2#usize } sum1 =
      ok (done sum1) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeDone2]

private theorem threeAroundInnerExact
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 value0 value1 contribution0 contribution1 sum0 sum1 :
      RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 2#usize } groupValues
        (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts31
        oneThreeFirstSlots V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok sum1 := by
  have step0 := threeAroundInnerStep0 group0 group1 groupValues coefficient0
    alpha3 value0 contribution0 sum0 value0Run contribution0Run sum0Run
  have step1 := threeAroundInnerStep1 group0 group1 groupValues coefficient0
    alpha3 value1 contribution1 sum0 sum1 value1Run contribution1Run sum1Run
  have done := threeAroundInnerDone group0 group1 groupValues coefficient0
    alpha3 sum1
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
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
  rw [done]

private theorem threeAroundOuterDone
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 value0 value1 contribution0
      contribution1 sum0 sum1 half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsThreeAround group0 group1) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 4#usize)
        (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts31
        oneThreeFirstSlots 2#usize = ok (done out) := by
  have innerRun := threeAroundInnerExact group0 group1 groupValues coefficient0
    alpha3 value0 value1 contribution0 contribution1 sum0 sum1 value0Run
    value1Run contribution0Run contribution1Run sum0Run sum1Run
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeDone4, innerRun, half1Run, outRun]

private theorem threeAroundOuterExact
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1
      contribution0 contribution1 sum0 sum1 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha2 =
        ok coefficient0)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add coefficient0 alpha =
        ok coefficient1)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient1 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
        (rangeFrom 0#usize) (groupsThreeAround group0 group1) groupValues
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0 slots0
        0#usize = ok out := by
  have step0 := threeAroundOuterStep0 group0 group1 groupValues alpha alpha2
    alpha3
  have step1 := threeAroundOuterStep1 group0 group1 different groupValues alpha
    alpha2 alpha3
  have step2 := threeAroundOuterStep2 group0 group1 groupValues alpha alpha2
    alpha3 coefficient0 coefficient0Run
  have step3 := threeAroundOuterStep3 group0 group1 groupValues alpha alpha2
    alpha3 coefficient0 coefficient1 coefficient1Run
  have done := threeAroundOuterDone group0 group1 groupValues alpha alpha2
    alpha3 coefficient1 value0 value1 contribution0 contribution1 sum0 sum1
    half1 out value0Run value1Run contribution0Run contribution1Run sum0Run
    sum1Run half1Run outRun
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

theorem threeAroundSourceExact
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1
      contribution0 contribution1 sum0 sum1 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha2 =
        ok coefficient0)
    (coefficient1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add coefficient0 alpha =
        ok coefficient1)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient1 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (groupsThreeAround group0 group1) groupValues alpha alpha2 alpha3 =
      ok out := by
  have run := threeAroundOuterExact group0 group1 different groupValues alpha
    alpha2 alpha3 coefficient0 coefficient1 value0 value1 contribution0
    contribution1 sum0 sum1 half1 out coefficient0Run coefficient1Run
    value0Run value1Run contribution0Run contribution1Run sum0Run sum1Run
    half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  simpa [rangeFrom, powers, unique0, coefficients0, slots0] using run

theorem threeAroundSourceCorresponds
    (group0 group1 : Std.U8) (different : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (value0 value1 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (groupsThreeAround group0 group1) groupValues alpha alpha2 alpha3 =
        ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value1,
            toMaintainedExact value0, toMaintainedExact value0] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha2
      oneCanonical alpha2Canonical
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical,
      coefficient1Exact⟩ :=
    generated_qm31_add_corresponds coefficient0 alpha coefficient0Canonical
      alphaCanonical
  obtain ⟨contribution0, contribution0Run, contribution0Canonical,
      contribution0Exact⟩ :=
    generated_qm31_mul_corresponds value0 coefficient1 value0Canonical
      coefficient1Canonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha3 value1Canonical
      alpha3Canonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0
      zeroCanonical contribution0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum1 sum1Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := threeAroundSourceExact group0 group1 different groupValues
    alpha alpha2 alpha3 coefficient0 coefficient1 value0 value1 contribution0
    contribution1 sum0 sum1 half1 out coefficient0Run coefficient1Run
    value0Run value1Run contribution0Run contribution1Run sum0Run sum1Run
    half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient0ExactM := congrArg oldQm31ToMaintained coefficient0Exact
  have coefficient1ExactM := congrArg oldQm31ToMaintained coefficient1Exact
  have contribution0ExactM := congrArg oldQm31ToMaintained contribution0Exact
  have contribution1ExactM := congrArg oldQm31ToMaintained contribution1Exact
  have sum0ExactM := congrArg oldQm31ToMaintained sum0Exact
  have sum1ExactM := congrArg oldQm31ToMaintained sum1Exact
  have half1ExactM := congrArg oldQm31ToMaintained half1Exact
  have outExactM := congrArg oldQm31ToMaintained outExact
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at half1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at outExactM
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
    _ = toMaintainedExact sum1 := half1ExactM
    _ = toMaintainedExact sum0 + toMaintainedExact contribution1 := sum1ExactM
    _ = (toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
          toMaintainedExact contribution0) +
        toMaintainedExact contribution1 := by rw [sum0ExactM]
    _ = toMaintainedExact value0 * toMaintainedExact coefficient1 +
        toMaintainedExact value1 * toMaintainedExact alpha3 := by
      rw [zeroExact, contribution0ExactM, contribution1ExactM]
      ring
    _ = toMaintainedExact value0 *
          (((1 : ExactQM31) + toMaintainedExact alpha ^ 2) +
            toMaintainedExact alpha) +
        toMaintainedExact value1 * toMaintainedExact alpha ^ 3 := by
      rw [coefficient1ExactM, coefficient0ExactM, oneExact, alpha2Exact,
        alpha3Exact]
    _ = toMaintainedExact value0 +
        toMaintainedExact alpha ^ 3 * toMaintainedExact value1 +
        toMaintainedExact alpha ^ 2 * toMaintainedExact value0 +
        toMaintainedExact alpha * toMaintainedExact value0 := by ring

/-! ## The released `[4, 5, 6, 6]` tuple -/

def groupsLastPair
    (group0 group1 group2 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group2, group2]

private def lastPairUnique3
    (group0 group1 group2 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group2, 0#u8]

private def lastPairCoefficients111
    (alpha3 alpha2 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE, alpha3, alpha2,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def lastPairCoefficientsFinal
    (alpha3 coefficient2 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE, alpha3, coefficient2,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def lastPairCounts111 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 1#u8, 0#u8]

private def lastPairCounts112 : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 2#u8, 0#u8]

private def lastPairFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 2#u8, 0#u8]

private theorem lastPairFindNewStep0
    (group0 group1 group2 : Std.U8) (different02 : group0 ≠ group2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (oneThreeUnique2 group0 group1) 2#usize group2 0#usize =
      ok (cont 1#usize) := by
  have indexRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 0#usize =
        ok group0 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index0 group0 group1 0#u8 0#u8)
  have differentVal : group0.val ≠ group2.val := by
    intro same
    apply different02
    apply UScalar.val_eq_imp
    exact same
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, differentVal, usizeZeroSucc, Std.lift]

private theorem lastPairFindNewStep1
    (group0 group1 group2 : Std.U8) (different12 : group1 ≠ group2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (oneThreeUnique2 group0 group1) 2#usize group2 1#usize =
      ok (cont 2#usize) := by
  have indexRun :
      Array.index_usize (oneThreeUnique2 group0 group1) 1#usize =
        ok group1 := by
    simpa [oneThreeUnique2] using
      (arrayMake4Index1 group0 group1 0#u8 0#u8)
  have differentVal : group1.val ≠ group2.val := by
    intro same
    apply different12
    apply UScalar.val_eq_imp
    exact same
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, differentVal, usizeOneSucc, Std.lift]

private theorem lastPairFindNewDone
    (group0 group1 group2 : Std.U8) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (oneThreeUnique2 group0 group1) 2#usize group2 2#usize =
      ok (done 2#usize) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body]

private theorem lastPairFindNew
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (oneThreeUnique2 group0 group1) 2#usize group2 0#usize =
      ok 2#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  rw [lastPairFindNewStep0 group0 group1 group2 different02]
  simp only
  rw [loop.eq_1]
  rw [lastPairFindNewStep1 group0 group1 group2 different12]
  simp only
  rw [loop.eq_1]
  rw [lastPairFindNewDone]

private theorem lastPairFindExistingStep0
    (group0 group1 group2 : Std.U8) (different02 : group0 ≠ group2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (lastPairUnique3 group0 group1 group2) 3#usize group2 0#usize =
      ok (cont 1#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 0#usize =
        ok group0 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index0 group0 group1 group2 0#u8)
  have differentVal : group0.val ≠ group2.val := by
    intro same
    apply different02
    apply UScalar.val_eq_imp
    exact same
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, differentVal, usizeZeroSucc, Std.lift]

private theorem lastPairFindExistingStep1
    (group0 group1 group2 : Std.U8) (different12 : group1 ≠ group2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (lastPairUnique3 group0 group1 group2) 3#usize group2 1#usize =
      ok (cont 2#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index1 group0 group1 group2 0#u8)
  have differentVal : group1.val ≠ group2.val := by
    intro same
    apply different12
    apply UScalar.val_eq_imp
    exact same
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, differentVal, usizeOneSucc, Std.lift]

private theorem lastPairFindExistingDone
    (group0 group1 group2 : Std.U8) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (lastPairUnique3 group0 group1 group2) 3#usize group2 2#usize =
      ok (done 2#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index2 group0 group1 group2 0#u8)
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun]

private theorem lastPairFindExisting
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (lastPairUnique3 group0 group1 group2) 3#usize group2 0#usize =
      ok 2#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  rw [lastPairFindExistingStep0 group0 group1 group2 different02]
  simp only
  rw [loop.eq_1]
  rw [lastPairFindExistingStep1 group0 group1 group2 different12]
  simp only
  rw [loop.eq_1]
  rw [lastPairFindExistingDone]

private theorem lastPairOuterStep0
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsLastPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 0#usize) unique0 coefficients0
        unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeNext0, allSameFindEmpty, groupsLastPair, powers, rangeFrom, unique0,
    unique1, coefficients0, coefficients1, countsAt, slots0,
    Array.index_usize, Array.update, UScalar.lt_equiv, Std.lift]
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

private theorem lastPairOuterStep1
    (group0 group1 group2 : Std.U8) (different01 : group0 ≠ group1)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsLastPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 1#usize) (unique1 group0)
        coefficients1 (countsAt 1#u8) slots0 1#usize =
      ok (cont (rangeFrom 2#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficients11 alpha3, oneThreeCounts11,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsLastPair group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [groupsLastPair] using
      (arrayMake4Index1 group0 group1 group2 group2)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 1#usize =
      ok alpha3 := by
    simpa [powers] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun,
    oneThreeFindNew group0 group1 different01, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, countsAt, slots0, oneThreeUnique2,
    threeAroundCoefficients11, oneThreeCounts11, oneThreeFirstSlots,
    Array.update, Std.lift, castUsizeOneU8, usizeOneSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem lastPairOuterStep2
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsLastPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 2#usize)
        (oneThreeUnique2 group0 group1) (threeAroundCoefficients11 alpha3)
        oneThreeCounts11 oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 3#usize, lastPairUnique3 group0 group1 group2,
        lastPairCoefficients111 alpha3 alpha2, lastPairCounts111,
        lastPairFirstSlots, 3#usize)) := by
  have groupRun :
      Array.index_usize (groupsLastPair group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [groupsLastPair] using
      (arrayMake4Index2 group0 group1 group2 group2)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun,
    lastPairFindNew group0 group1 group2 different02 different12, powerRun]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficients11, oneThreeCounts11,
    oneThreeFirstSlots, lastPairUnique3, lastPairCoefficients111,
    lastPairCounts111, lastPairFirstSlots, Array.update, Std.lift,
    castUsizeTwoU8, usizeTwoSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem lastPairOuterStep3
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient2 : RawQM31)
    (coefficient2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha2 alpha =
        ok coefficient2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsLastPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 3#usize)
        (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficients111 alpha3 alpha2) lastPairCounts111
        lastPairFirstSlots 3#usize =
      ok (cont (rangeFrom 4#usize, lastPairUnique3 group0 group1 group2,
        lastPairCoefficientsFinal alpha3 coefficient2, lastPairCounts112,
        lastPairFirstSlots, 3#usize)) := by
  have groupRun :
      Array.index_usize (groupsLastPair group0 group1 group2) 3#usize =
        ok group2 := by
    simpa [groupsLastPair] using
      (arrayMake4Index3 group0 group1 group2 group2)
  have coefficientRun :
      Array.index_usize (lastPairCoefficients111 alpha3 alpha2) 2#usize =
        ok alpha2 := by
    simpa [lastPairCoefficients111] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 alpha2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize lastPairCounts111 2#usize = ok 1#u8 := by
    simpa [lastPairCounts111] using
      (arrayMake4Index2 1#u8 1#u8 1#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    lastPairFindExisting group0 group1 group2 different02 different12,
    coefficientRun, powerRun, coefficient2Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [lastPairUnique3, lastPairCoefficients111, lastPairCoefficientsFinal,
    lastPairCounts111, lastPairCounts112, lastPairFirstSlots, Array.update,
    Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem rangeNext0End3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 3#usize } =
      ok (some 0#usize, { start := 1#usize, «end» := 3#usize }) := by
  have hmax : 0 < UScalar.max .Usize := by
    have h := (1#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext1End3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 3#usize } =
      ok (some 1#usize, { start := 2#usize, «end» := 3#usize }) := by
  have hmax : 1 < UScalar.max .Usize := by
    have h := (2#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeNext2End3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := 3#usize } =
      ok (some 2#usize, { start := 3#usize, «end» := 3#usize }) := by
  have hmax : 2 < UScalar.max .Usize := by
    have h := (3#usize).hBounds
    scalar_tac
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem rangeDone3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 3#usize, «end» := 3#usize } =
      ok (none, { start := 3#usize, «end» := 3#usize }) := by
  simp [core.iter.range.IteratorRange.next,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

private theorem lastPairInnerStep0
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 value0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots { start := 0#usize, «end» := 3#usize }
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 3#usize }, sum0)) := by
  have uniqueRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 0#usize =
        ok group0 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index0 group0 group1 group2 0#u8)
  have firstSlotRun :
      Array.index_usize lastPairFirstSlots 0#usize = ok 0#u8 := by
    simpa [lastPairFirstSlots] using
      (arrayMake4Index0 0#u8 1#u8 2#u8 0#u8)
  have countRun : Array.index_usize lastPairCounts112 0#usize = ok 1#u8 := by
    simpa [lastPairCounts112] using
      (arrayMake4Index0 1#u8 1#u8 2#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext0End3, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, sum0Run, Std.lift]

private theorem lastPairInnerStep1
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots { start := 1#usize, «end» := 3#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 3#usize }, sum1)) := by
  have uniqueRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index1 group0 group1 group2 0#u8)
  have firstSlotRun :
      Array.index_usize lastPairFirstSlots 1#usize = ok 1#u8 := by
    simpa [lastPairFirstSlots] using
      (arrayMake4Index1 0#u8 1#u8 2#u8 0#u8)
  have coefficientRun :
      Array.index_usize (lastPairCoefficientsFinal alpha3 coefficient2)
          1#usize = ok alpha3 := by
    simpa [lastPairCoefficientsFinal] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 coefficient2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext1End3, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem lastPairInnerStep2
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 value2 contribution2 sum1 sum2 : RawQM31)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots { start := 2#usize, «end» := 3#usize } sum1 =
      ok (cont ({ start := 3#usize, «end» := 3#usize }, sum2)) := by
  have uniqueRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index2 group0 group1 group2 0#u8)
  have firstSlotRun :
      Array.index_usize lastPairFirstSlots 2#usize = ok 2#u8 := by
    simpa [lastPairFirstSlots] using
      (arrayMake4Index2 0#u8 1#u8 2#u8 0#u8)
  have coefficientRun :
      Array.index_usize (lastPairCoefficientsFinal alpha3 coefficient2)
          2#usize = ok coefficient2 := by
    simpa [lastPairCoefficientsFinal] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 coefficient2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext2End3, uniqueRun, fromU8ToUsizeExact, value2Run, firstSlotRun,
    coefficientRun, contribution2Run, sum2Run, Std.lift]

private theorem lastPairInnerDone
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 sum2 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots { start := 3#usize, «end» := 3#usize } sum2 =
      ok (done sum2) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeDone3]

private theorem lastPairInnerExact
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha3 coefficient2 value0 value1 value2 contribution1 contribution2
      sum0 sum1 sum2 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 3#usize } groupValues
        (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok sum2 := by
  have step0 := lastPairInnerStep0 group0 group1 group2 groupValues alpha3
    coefficient2 value0 sum0 value0Run sum0Run
  have step1 := lastPairInnerStep1 group0 group1 group2 groupValues alpha3
    coefficient2 value1 contribution1 sum0 sum1 value1Run contribution1Run
    sum1Run
  have step2 := lastPairInnerStep2 group0 group1 group2 groupValues alpha3
    coefficient2 value2 contribution2 sum1 sum2 value2Run contribution2Run
    sum2Run
  have done := lastPairInnerDone group0 group1 group2 groupValues alpha3
    coefficient2 sum2
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
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
  rw [done]

private theorem lastPairOuterDone
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient2 value0 value1 value2 contribution1
      contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum2 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsLastPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 4#usize)
        (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficientsFinal alpha3 coefficient2) lastPairCounts112
        lastPairFirstSlots 3#usize = ok (done out) := by
  have innerRun := lastPairInnerExact group0 group1 group2 groupValues alpha3
    coefficient2 value0 value1 value2 contribution1 contribution2 sum0 sum1
    sum2 value0Run value1Run value2Run contribution1Run contribution2Run
    sum0Run sum1Run sum2Run
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeDone4, innerRun, half1Run, outRun]

private theorem lastPairOuterExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient2 value0 value1 value2 contribution1
      contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (coefficient2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha2 alpha =
        ok coefficient2)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum2 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
        (rangeFrom 0#usize) (groupsLastPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0 slots0
        0#usize = ok out := by
  have step0 := lastPairOuterStep0 group0 group1 group2 groupValues alpha
    alpha2 alpha3
  have step1 := lastPairOuterStep1 group0 group1 group2 different01 groupValues
    alpha alpha2 alpha3
  have step2 := lastPairOuterStep2 group0 group1 group2 different02 different12
    groupValues alpha alpha2 alpha3
  have step3 := lastPairOuterStep3 group0 group1 group2 different02 different12
    groupValues alpha alpha2 alpha3 coefficient2 coefficient2Run
  have done := lastPairOuterDone group0 group1 group2 groupValues alpha alpha2
    alpha3 coefficient2 value0 value1 value2 contribution1 contribution2 sum0
    sum1 sum2 half1 out value0Run value1Run value2Run contribution1Run
    contribution2Run sum0Run sum1Run sum2Run half1Run outRun
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

theorem lastPairSourceExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient2 value0 value1 value2 contribution1
      contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (coefficient2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha2 alpha =
        ok coefficient2)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum2 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (groupsLastPair group0 group1 group2) groupValues alpha alpha2 alpha3 =
      ok out := by
  have run := lastPairOuterExact group0 group1 group2 different01 different02
    different12 groupValues alpha alpha2 alpha3 coefficient2 value0 value1
    value2 contribution1 contribution2 sum0 sum1 sum2 half1 out
    coefficient2Run value0Run value1Run value2Run contribution1Run
    contribution2Run sum0Run sum1Run sum2Run half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  simpa [rangeFrom, powers, unique0, coefficients0, slots0] using run

theorem lastPairSourceCorresponds
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (value0 value1 value2 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (value2Canonical : CanonicalQM31 value2)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (groupsLastPair group0 group1 group2) groupValues alpha alpha2 alpha3 =
        ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value1,
            toMaintainedExact value2, toMaintainedExact value2] index) := by
  obtain ⟨coefficient2, coefficient2Run, coefficient2Canonical,
      coefficient2Exact⟩ :=
    generated_qm31_add_corresponds alpha2 alpha alpha2Canonical alphaCanonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha3 value1Canonical
      alpha3Canonical
  obtain ⟨contribution2, contribution2Run, contribution2Canonical,
      contribution2Exact⟩ :=
    generated_qm31_mul_corresponds value2 coefficient2 value2Canonical
      coefficient2Canonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0
      zeroCanonical value0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨sum2, sum2Run, sum2Canonical, sum2Exact⟩ :=
    generated_qm31_add_corresponds sum1 contribution2 sum1Canonical
      contribution2Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum2 sum2Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := lastPairSourceExact group0 group1 group2 different01
    different02 different12 groupValues alpha alpha2 alpha3 coefficient2
    value0 value1 value2 contribution1 contribution2 sum0 sum1 sum2 half1 out
    coefficient2Run value0Run value1Run value2Run contribution1Run
    contribution2Run sum0Run sum1Run sum2Run half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient2ExactM := congrArg oldQm31ToMaintained coefficient2Exact
  have contribution1ExactM := congrArg oldQm31ToMaintained contribution1Exact
  have contribution2ExactM := congrArg oldQm31ToMaintained contribution2Exact
  have sum0ExactM := congrArg oldQm31ToMaintained sum0Exact
  have sum1ExactM := congrArg oldQm31ToMaintained sum1Exact
  have sum2ExactM := congrArg oldQm31ToMaintained sum2Exact
  have half1ExactM := congrArg oldQm31ToMaintained half1Exact
  have outExactM := congrArg oldQm31ToMaintained outExact
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient2ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution2ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum2ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at half1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at outExactM
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
    _ = toMaintainedExact sum2 := half1ExactM
    _ = toMaintainedExact sum1 + toMaintainedExact contribution2 := sum2ExactM
    _ = (toMaintainedExact sum0 + toMaintainedExact contribution1) +
        toMaintainedExact contribution2 := by rw [sum1ExactM]
    _ = ((toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
          toMaintainedExact value0) + toMaintainedExact contribution1) +
        toMaintainedExact contribution2 := by rw [sum0ExactM]
    _ = toMaintainedExact value0 +
        toMaintainedExact value1 * toMaintainedExact alpha3 +
        toMaintainedExact value2 * toMaintainedExact coefficient2 := by
      rw [zeroExact, contribution1ExactM, contribution2ExactM]
      ring
    _ = toMaintainedExact value0 +
        toMaintainedExact value1 * toMaintainedExact alpha ^ 3 +
        toMaintainedExact value2 *
          (toMaintainedExact alpha ^ 2 + toMaintainedExact alpha) := by
      rw [coefficient2ExactM, alpha2Exact, alpha3Exact]
    _ = toMaintainedExact value0 +
        toMaintainedExact alpha ^ 3 * toMaintainedExact value1 +
        toMaintainedExact alpha ^ 2 * toMaintainedExact value2 +
        toMaintainedExact alpha * toMaintainedExact value2 := by ring

/-! ## Shared three-value inner fold where every contribution is multiplied -/

private theorem threeMultiplyInnerStep0
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize)
    (group0 firstSlot0 count0 : Std.U8)
    (coefficient0 value0 contribution0 sum0 : RawQM31)
    (uniqueRun : Array.index_usize uniqueGroups 0#usize = ok group0)
    (firstSlotRun : Array.index_usize firstSlots 0#usize = ok firstSlot0)
    (countRun : Array.index_usize counts 0#usize = ok count0)
    (firstSlotZero : firstSlot0 = 0#u8)
    (countNotOne : count0 ≠ 1#u8)
    (coefficientRun :
      Array.index_usize coefficients 0#usize = ok coefficient0)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (contributionRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (sumRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues uniqueGroups coefficients counts firstSlots
        { start := 0#usize, «end» := 3#usize }
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 3#usize }, sum0)) := by
  subst firstSlot0
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext0End3, uniqueRun, fromU8ToUsizeExact, valueRun, firstSlotRun,
    countRun, countNotOne, coefficientRun, contributionRun, sumRun, Std.lift]

private theorem threeMultiplyInnerStep1
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize)
    (group1 firstSlot1 : Std.U8)
    (coefficient1 value1 contribution1 sum0 sum1 : RawQM31)
    (uniqueRun : Array.index_usize uniqueGroups 1#usize = ok group1)
    (firstSlotRun : Array.index_usize firstSlots 1#usize = ok firstSlot1)
    (firstSlotNotZero : firstSlot1 ≠ 0#u8)
    (coefficientRun :
      Array.index_usize coefficients 1#usize = ok coefficient1)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contributionRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (sumRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues uniqueGroups coefficients counts firstSlots
        { start := 1#usize, «end» := 3#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 3#usize }, sum1)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext1End3, uniqueRun, fromU8ToUsizeExact, valueRun, firstSlotRun,
    firstSlotNotZero, coefficientRun, contributionRun, sumRun, Std.lift]

private theorem threeMultiplyInnerStep2
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize)
    (group2 firstSlot2 : Std.U8)
    (coefficient2 value2 contribution2 sum1 sum2 : RawQM31)
    (uniqueRun : Array.index_usize uniqueGroups 2#usize = ok group2)
    (firstSlotRun : Array.index_usize firstSlots 2#usize = ok firstSlot2)
    (firstSlotNotZero : firstSlot2 ≠ 0#u8)
    (coefficientRun :
      Array.index_usize coefficients 2#usize = ok coefficient2)
    (valueRun :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contributionRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sumRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues uniqueGroups coefficients counts firstSlots
        { start := 2#usize, «end» := 3#usize } sum1 =
      ok (cont ({ start := 3#usize, «end» := 3#usize }, sum2)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext2End3, uniqueRun, fromU8ToUsizeExact, valueRun, firstSlotRun,
    firstSlotNotZero, coefficientRun, contributionRun, sumRun, Std.lift]

private theorem threeMultiplyInnerDone
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize) (sum2 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues uniqueGroups coefficients counts firstSlots
        { start := 3#usize, «end» := 3#usize } sum2 = ok (done sum2) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeDone3]

private theorem threeMultiplyInnerExact
    (groupValues : Slice RawQM31)
    (uniqueGroups : Array Std.U8 4#usize)
    (coefficients : Array RawQM31 4#usize)
    (counts firstSlots : Array Std.U8 4#usize)
    (group0 group1 group2 firstSlot0 count0 firstSlot1 firstSlot2 : Std.U8)
    (coefficient0 coefficient1 coefficient2 value0 value1 value2
      contribution0 contribution1 contribution2 sum0 sum1 sum2 : RawQM31)
    (unique0Run : Array.index_usize uniqueGroups 0#usize = ok group0)
    (unique1Run : Array.index_usize uniqueGroups 1#usize = ok group1)
    (unique2Run : Array.index_usize uniqueGroups 2#usize = ok group2)
    (firstSlot0Run : Array.index_usize firstSlots 0#usize = ok firstSlot0)
    (firstSlot1Run : Array.index_usize firstSlots 1#usize = ok firstSlot1)
    (firstSlot2Run : Array.index_usize firstSlots 2#usize = ok firstSlot2)
    (count0Run : Array.index_usize counts 0#usize = ok count0)
    (firstSlot0Zero : firstSlot0 = 0#u8)
    (count0NotOne : count0 ≠ 1#u8)
    (firstSlot1NotZero : firstSlot1 ≠ 0#u8)
    (firstSlot2NotZero : firstSlot2 ≠ 0#u8)
    (coefficient0Run : Array.index_usize coefficients 0#usize = ok coefficient0)
    (coefficient1Run : Array.index_usize coefficients 1#usize = ok coefficient1)
    (coefficient2Run : Array.index_usize coefficients 2#usize = ok coefficient2)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 coefficient1 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 coefficient2 = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 3#usize } groupValues uniqueGroups
        coefficients counts firstSlots
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO = ok sum2 := by
  have step0 := threeMultiplyInnerStep0 groupValues uniqueGroups coefficients
    counts firstSlots group0 firstSlot0 count0 coefficient0 value0
    contribution0 sum0 unique0Run firstSlot0Run count0Run firstSlot0Zero
    count0NotOne coefficient0Run value0Run contribution0Run sum0Run
  have step1 := threeMultiplyInnerStep1 groupValues uniqueGroups coefficients
    counts firstSlots group1 firstSlot1 coefficient1 value1 contribution1 sum0
    sum1 unique1Run firstSlot1Run firstSlot1NotZero coefficient1Run value1Run
    contribution1Run sum1Run
  have step2 := threeMultiplyInnerStep2 groupValues uniqueGroups coefficients
    counts firstSlots group2 firstSlot2 coefficient2 value2 contribution2 sum1
    sum2 unique2Run firstSlot2Run firstSlot2NotZero coefficient2Run value2Run
    contribution2Run sum2Run
  have done := threeMultiplyInnerDone groupValues uniqueGroups coefficients
    counts firstSlots sum2
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
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
  rw [done]

/-! ## The released `[0, 2, 0, 1]` tuple -/

def groupsSplitPair
    (group0 group1 group2 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group0, group2]

private def splitPairCoefficientsFinal
    (coefficient0 alpha3 alpha : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0, alpha3, alpha,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def splitPairCounts211 : Array Std.U8 4#usize :=
  Array.make 4#usize [2#u8, 1#u8, 1#u8, 0#u8]

private def splitPairFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 3#u8, 0#u8]

private theorem splitPairOuterStep0
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsSplitPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 0#usize) unique0 coefficients0
        unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeNext0, allSameFindEmpty, groupsSplitPair, powers, rangeFrom, unique0,
    unique1, coefficients0, coefficients1, countsAt, slots0,
    Array.index_usize, Array.update, UScalar.lt_equiv, Std.lift]
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

private theorem splitPairOuterStep1
    (group0 group1 group2 : Std.U8) (different01 : group0 ≠ group1)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsSplitPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 1#usize) (unique1 group0)
        coefficients1 (countsAt 1#u8) slots0 1#usize =
      ok (cont (rangeFrom 2#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficients11 alpha3, oneThreeCounts11,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsSplitPair group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [groupsSplitPair] using
      (arrayMake4Index1 group0 group1 group0 group2)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 1#usize =
      ok alpha3 := by
    simpa [powers] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun,
    oneThreeFindNew group0 group1 different01, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, countsAt, slots0, oneThreeUnique2,
    threeAroundCoefficients11, oneThreeCounts11, oneThreeFirstSlots,
    Array.update, Std.lift, castUsizeOneU8, usizeOneSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem splitPairOuterStep2
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha2 =
        ok coefficient0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsSplitPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 2#usize)
        (oneThreeUnique2 group0 group1) (threeAroundCoefficients11 alpha3)
        oneThreeCounts11 oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 3#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficientsAt coefficient0 alpha3, threeAroundCounts21,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsSplitPair group0 group1 group2) 2#usize =
        ok group0 := by
    simpa [groupsSplitPair] using
      (arrayMake4Index2 group0 group1 group0 group2)
  have coefficientRun :
      Array.index_usize (threeAroundCoefficients11 alpha3) 0#usize =
        ok V5RelationLinkedGenerated.aspis_core.field.QM31.ONE := by
    simpa [threeAroundCoefficients11] using
      (arrayMake4Index0
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  have countRun : Array.index_usize oneThreeCounts11 0#usize = ok 1#u8 := by
    simpa [oneThreeCounts11] using
      (arrayMake4Index0 1#u8 1#u8 0#u8 0#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun,
    threeAroundFindFirst group0 group1, coefficientRun, powerRun,
    coefficient0Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficients11,
    threeAroundCoefficientsAt, oneThreeCounts11, threeAroundCounts21,
    oneThreeFirstSlots, Array.update, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem splitPairOuterStep3
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsSplitPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 3#usize)
        (oneThreeUnique2 group0 group1)
        (threeAroundCoefficientsAt coefficient0 alpha3) threeAroundCounts21
        oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 4#usize, lastPairUnique3 group0 group1 group2,
        splitPairCoefficientsFinal coefficient0 alpha3 alpha,
        splitPairCounts211, splitPairFirstSlots, 3#usize)) := by
  have groupRun :
      Array.index_usize (groupsSplitPair group0 group1 group2) 3#usize =
        ok group2 := by
    simpa [groupsSplitPair] using
      (arrayMake4Index3 group0 group1 group0 group2)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    lastPairFindNew group0 group1 group2 different02 different12, powerRun]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficientsAt, threeAroundCounts21,
    oneThreeFirstSlots, lastPairUnique3, splitPairCoefficientsFinal,
    splitPairCounts211, splitPairFirstSlots, Array.update, Std.lift,
    castUsizeThreeU8, usizeTwoSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem splitPairInnerExact
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha3 alpha value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 3#usize } groupValues
        (lastPairUnique3 group0 group1 group2)
        (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
        splitPairCounts211 splitPairFirstSlots
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO = ok sum2 := by
  have unique0Run :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 0#usize =
        ok group0 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index0 group0 group1 group2 0#u8)
  have unique1Run :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index1 group0 group1 group2 0#u8)
  have unique2Run :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index2 group0 group1 group2 0#u8)
  have firstSlot0Run :
      Array.index_usize splitPairFirstSlots 0#usize = ok 0#u8 := by
    simpa [splitPairFirstSlots] using
      (arrayMake4Index0 0#u8 1#u8 3#u8 0#u8)
  have firstSlot1Run :
      Array.index_usize splitPairFirstSlots 1#usize = ok 1#u8 := by
    simpa [splitPairFirstSlots] using
      (arrayMake4Index1 0#u8 1#u8 3#u8 0#u8)
  have firstSlot2Run :
      Array.index_usize splitPairFirstSlots 2#usize = ok 3#u8 := by
    simpa [splitPairFirstSlots] using
      (arrayMake4Index2 0#u8 1#u8 3#u8 0#u8)
  have count0Run : Array.index_usize splitPairCounts211 0#usize = ok 2#u8 := by
    simpa [splitPairCounts211] using
      (arrayMake4Index0 2#u8 1#u8 1#u8 0#u8)
  have coefficient0Run :
      Array.index_usize (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
          0#usize = ok coefficient0 := by
    simpa [splitPairCoefficientsFinal] using
      (arrayMake4Index0 coefficient0 alpha3 alpha
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have coefficient1Run :
      Array.index_usize (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
          1#usize = ok alpha3 := by
    simpa [splitPairCoefficientsFinal] using
      (arrayMake4Index1 coefficient0 alpha3 alpha
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have coefficient2Run :
      Array.index_usize (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
          2#usize = ok alpha := by
    simpa [splitPairCoefficientsFinal] using
      (arrayMake4Index2 coefficient0 alpha3 alpha
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  exact threeMultiplyInnerExact groupValues
    (lastPairUnique3 group0 group1 group2)
    (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
    splitPairCounts211 splitPairFirstSlots group0 group1 group2 0#u8 2#u8
    1#u8 3#u8 coefficient0 alpha3 alpha value0 value1 value2 contribution0
    contribution1 contribution2 sum0 sum1 sum2 unique0Run unique1Run
    unique2Run firstSlot0Run firstSlot1Run firstSlot2Run count0Run rfl
    (by decide) (by decide) (by decide) coefficient0Run coefficient1Run
    coefficient2Run value0Run value1Run value2Run contribution0Run
    contribution1Run contribution2Run sum0Run sum1Run sum2Run

private theorem splitPairOuterDone
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum2 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsSplitPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 4#usize)
        (lastPairUnique3 group0 group1 group2)
        (splitPairCoefficientsFinal coefficient0 alpha3 alpha)
        splitPairCounts211 splitPairFirstSlots 3#usize = ok (done out) := by
  have innerRun := splitPairInnerExact group0 group1 group2 groupValues
    coefficient0 alpha3 alpha value0 value1 value2 contribution0 contribution1
    contribution2 sum0 sum1 sum2 value0Run value1Run value2Run
    contribution0Run contribution1Run contribution2Run sum0Run sum1Run sum2Run
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeDone4, innerRun, half1Run, outRun]

private theorem splitPairOuterExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha2 =
        ok coefficient0)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum2 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
        (rangeFrom 0#usize) (groupsSplitPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0 slots0
        0#usize = ok out := by
  have step0 := splitPairOuterStep0 group0 group1 group2 groupValues alpha
    alpha2 alpha3
  have step1 := splitPairOuterStep1 group0 group1 group2 different01 groupValues
    alpha alpha2 alpha3
  have step2 := splitPairOuterStep2 group0 group1 group2 groupValues alpha
    alpha2 alpha3 coefficient0 coefficient0Run
  have step3 := splitPairOuterStep3 group0 group1 group2 different02 different12
    groupValues alpha alpha2 alpha3 coefficient0
  have done := splitPairOuterDone group0 group1 group2 groupValues alpha alpha2
    alpha3 coefficient0 value0 value1 value2 contribution0 contribution1
    contribution2 sum0 sum1 sum2 half1 out value0Run value1Run value2Run
    contribution0Run contribution1Run contribution2Run sum0Run sum1Run sum2Run
    half1Run outRun
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

theorem splitPairSourceExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha2 =
        ok coefficient0)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum2 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (groupsSplitPair group0 group1 group2) groupValues alpha alpha2 alpha3 =
      ok out := by
  have run := splitPairOuterExact group0 group1 group2 different01 different02
    different12 groupValues alpha alpha2 alpha3 coefficient0 value0 value1
    value2 contribution0 contribution1 contribution2 sum0 sum1 sum2 half1 out
    coefficient0Run value0Run value1Run value2Run contribution0Run
    contribution1Run contribution2Run sum0Run sum1Run sum2Run half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  simpa [rangeFrom, powers, unique0, coefficients0, slots0] using run

theorem splitPairSourceCorresponds
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (value0 value1 value2 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (value2Canonical : CanonicalQM31 value2)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (groupsSplitPair group0 group1 group2) groupValues alpha alpha2 alpha3 =
        ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value1,
            toMaintainedExact value0, toMaintainedExact value2] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha2
      oneCanonical alpha2Canonical
  obtain ⟨contribution0, contribution0Run, contribution0Canonical,
      contribution0Exact⟩ :=
    generated_qm31_mul_corresponds value0 coefficient0 value0Canonical
      coefficient0Canonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha3 value1Canonical
      alpha3Canonical
  obtain ⟨contribution2, contribution2Run, contribution2Canonical,
      contribution2Exact⟩ :=
    generated_qm31_mul_corresponds value2 alpha value2Canonical alphaCanonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0
      zeroCanonical contribution0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨sum2, sum2Run, sum2Canonical, sum2Exact⟩ :=
    generated_qm31_add_corresponds sum1 contribution2 sum1Canonical
      contribution2Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum2 sum2Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := splitPairSourceExact group0 group1 group2 different01
    different02 different12 groupValues alpha alpha2 alpha3 coefficient0
    value0 value1 value2 contribution0 contribution1 contribution2 sum0 sum1
    sum2 half1 out coefficient0Run value0Run value1Run value2Run
    contribution0Run contribution1Run contribution2Run sum0Run sum1Run sum2Run
    half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient0ExactM := congrArg oldQm31ToMaintained coefficient0Exact
  have contribution0ExactM := congrArg oldQm31ToMaintained contribution0Exact
  have contribution1ExactM := congrArg oldQm31ToMaintained contribution1Exact
  have contribution2ExactM := congrArg oldQm31ToMaintained contribution2Exact
  have sum0ExactM := congrArg oldQm31ToMaintained sum0Exact
  have sum1ExactM := congrArg oldQm31ToMaintained sum1Exact
  have sum2ExactM := congrArg oldQm31ToMaintained sum2Exact
  have half1ExactM := congrArg oldQm31ToMaintained half1Exact
  have outExactM := congrArg oldQm31ToMaintained outExact
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution2ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum2ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at half1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at outExactM
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
    _ = toMaintainedExact sum2 := half1ExactM
    _ = toMaintainedExact sum1 + toMaintainedExact contribution2 := sum2ExactM
    _ = (toMaintainedExact sum0 + toMaintainedExact contribution1) +
        toMaintainedExact contribution2 := by rw [sum1ExactM]
    _ = ((toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
          toMaintainedExact contribution0) + toMaintainedExact contribution1) +
        toMaintainedExact contribution2 := by rw [sum0ExactM]
    _ = toMaintainedExact value0 * toMaintainedExact coefficient0 +
        toMaintainedExact value1 * toMaintainedExact alpha3 +
        toMaintainedExact value2 * toMaintainedExact alpha := by
      rw [zeroExact, contribution0ExactM, contribution1ExactM,
        contribution2ExactM]
      ring
    _ = toMaintainedExact value0 *
          ((1 : ExactQM31) + toMaintainedExact alpha ^ 2) +
        toMaintainedExact value1 * toMaintainedExact alpha ^ 3 +
        toMaintainedExact value2 * toMaintainedExact alpha := by
      rw [coefficient0ExactM, oneExact, alpha2Exact, alpha3Exact]
    _ = toMaintainedExact value0 +
        toMaintainedExact alpha ^ 3 * toMaintainedExact value1 +
        toMaintainedExact alpha ^ 2 * toMaintainedExact value0 +
        toMaintainedExact alpha * toMaintainedExact value2 := by ring

/-! ## The released `[1, 1, 2, 3]` tuple -/

def groupsFirstPair
    (group0 group1 group2 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group0, group1, group2]

private def firstPairCoefficientsAt
    (coefficient0 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def firstPairCounts2 : Array Std.U8 4#usize :=
  Array.make 4#usize [2#u8, 0#u8, 0#u8, 0#u8]

private def firstPairCoefficients21
    (coefficient0 alpha2 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0, alpha2,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def firstPairFirstSlots02 : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 2#u8, 0#u8, 0#u8]

private def firstPairCoefficientsFinal
    (coefficient0 alpha2 alpha : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [coefficient0, alpha2, alpha,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]

private def firstPairFirstSlots023 : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 2#u8, 3#u8, 0#u8]

private theorem firstPairOuterStep0
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsFirstPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 0#usize) unique0 coefficients0
        unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeNext0, allSameFindEmpty, groupsFirstPair, powers, rangeFrom, unique0,
    unique1, coefficients0, coefficients1, countsAt, slots0,
    Array.index_usize, Array.update, UScalar.lt_equiv, Std.lift]
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

private theorem firstPairOuterStep1
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsFirstPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 1#usize) (unique1 group0)
        coefficients1 (countsAt 1#u8) slots0 1#usize =
      ok (cont (rangeFrom 2#usize, unique1 group0,
        firstPairCoefficientsAt coefficient0, firstPairCounts2, slots0,
        1#usize)) := by
  have groupRun :
      Array.index_usize (groupsFirstPair group0 group1 group2) 1#usize =
        ok group0 := by
    simpa [groupsFirstPair] using
      (arrayMake4Index1 group0 group0 group1 group2)
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
    rangeFrom, rangeNext1, groupRun, allSameFindExisting, coefficientRun,
    powerRun, coefficient0Run, countRun, u8OneSucc]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, firstPairCoefficientsAt, countsAt,
    firstPairCounts2, slots0, Array.update, Std.lift]
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem firstPairOuterStep2
    (group0 group1 group2 : Std.U8) (different01 : group0 ≠ group1)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsFirstPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 2#usize) (unique1 group0)
        (firstPairCoefficientsAt coefficient0) firstPairCounts2 slots0
        1#usize =
      ok (cont (rangeFrom 3#usize, oneThreeUnique2 group0 group1,
        firstPairCoefficients21 coefficient0 alpha2, threeAroundCounts21,
        firstPairFirstSlots02, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsFirstPair group0 group1 group2) 2#usize =
        ok group1 := by
    simpa [groupsFirstPair] using
      (arrayMake4Index2 group0 group0 group1 group2)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun,
    oneThreeFindNew group0 group1 different01, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, firstPairCoefficientsAt, firstPairCounts2, slots0,
    oneThreeUnique2, firstPairCoefficients21, threeAroundCounts21,
    firstPairFirstSlots02, Array.update, Std.lift, castUsizeTwoU8,
    usizeOneSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem firstPairOuterStep3
    (group0 group1 group2 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsFirstPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 3#usize)
        (oneThreeUnique2 group0 group1)
        (firstPairCoefficients21 coefficient0 alpha2) threeAroundCounts21
        firstPairFirstSlots02 2#usize =
      ok (cont (rangeFrom 4#usize, lastPairUnique3 group0 group1 group2,
        firstPairCoefficientsFinal coefficient0 alpha2 alpha,
        splitPairCounts211, firstPairFirstSlots023, 3#usize)) := by
  have groupRun :
      Array.index_usize (groupsFirstPair group0 group1 group2) 3#usize =
        ok group2 := by
    simpa [groupsFirstPair] using
      (arrayMake4Index3 group0 group0 group1 group2)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    lastPairFindNew group0 group1 group2 different02 different12, powerRun]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, firstPairCoefficients21, threeAroundCounts21,
    firstPairFirstSlots02, lastPairUnique3, firstPairCoefficientsFinal,
    splitPairCounts211, firstPairFirstSlots023, Array.update, Std.lift,
    castUsizeThreeU8, usizeTwoSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem firstPairInnerExact
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (coefficient0 alpha2 alpha value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha2 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 3#usize } groupValues
        (lastPairUnique3 group0 group1 group2)
        (firstPairCoefficientsFinal coefficient0 alpha2 alpha)
        splitPairCounts211 firstPairFirstSlots023
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO = ok sum2 := by
  have unique0Run :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 0#usize =
        ok group0 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index0 group0 group1 group2 0#u8)
  have unique1Run :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index1 group0 group1 group2 0#u8)
  have unique2Run :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index2 group0 group1 group2 0#u8)
  have firstSlot0Run :
      Array.index_usize firstPairFirstSlots023 0#usize = ok 0#u8 := by
    simpa [firstPairFirstSlots023] using
      (arrayMake4Index0 0#u8 2#u8 3#u8 0#u8)
  have firstSlot1Run :
      Array.index_usize firstPairFirstSlots023 1#usize = ok 2#u8 := by
    simpa [firstPairFirstSlots023] using
      (arrayMake4Index1 0#u8 2#u8 3#u8 0#u8)
  have firstSlot2Run :
      Array.index_usize firstPairFirstSlots023 2#usize = ok 3#u8 := by
    simpa [firstPairFirstSlots023] using
      (arrayMake4Index2 0#u8 2#u8 3#u8 0#u8)
  have count0Run : Array.index_usize splitPairCounts211 0#usize = ok 2#u8 := by
    simpa [splitPairCounts211] using
      (arrayMake4Index0 2#u8 1#u8 1#u8 0#u8)
  have coefficient0Run :
      Array.index_usize (firstPairCoefficientsFinal coefficient0 alpha2 alpha)
          0#usize = ok coefficient0 := by
    simpa [firstPairCoefficientsFinal] using
      (arrayMake4Index0 coefficient0 alpha2 alpha
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have coefficient1Run :
      Array.index_usize (firstPairCoefficientsFinal coefficient0 alpha2 alpha)
          1#usize = ok alpha2 := by
    simpa [firstPairCoefficientsFinal] using
      (arrayMake4Index1 coefficient0 alpha2 alpha
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  have coefficient2Run :
      Array.index_usize (firstPairCoefficientsFinal coefficient0 alpha2 alpha)
          2#usize = ok alpha := by
    simpa [firstPairCoefficientsFinal] using
      (arrayMake4Index2 coefficient0 alpha2 alpha
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO)
  exact threeMultiplyInnerExact groupValues
    (lastPairUnique3 group0 group1 group2)
    (firstPairCoefficientsFinal coefficient0 alpha2 alpha)
    splitPairCounts211 firstPairFirstSlots023 group0 group1 group2 0#u8 2#u8
    2#u8 3#u8 coefficient0 alpha2 alpha value0 value1 value2 contribution0
    contribution1 contribution2 sum0 sum1 sum2 unique0Run unique1Run
    unique2Run firstSlot0Run firstSlot1Run firstSlot2Run count0Run rfl
    (by decide) (by decide) (by decide) coefficient0Run coefficient1Run
    coefficient2Run value0Run value1Run value2Run contribution0Run
    contribution1Run contribution2Run sum0Run sum1Run sum2Run

private theorem firstPairOuterDone
    (group0 group1 group2 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha2 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum2 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsFirstPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 4#usize)
        (lastPairUnique3 group0 group1 group2)
        (firstPairCoefficientsFinal coefficient0 alpha2 alpha)
        splitPairCounts211 firstPairFirstSlots023 3#usize = ok (done out) := by
  have innerRun := firstPairInnerExact group0 group1 group2 groupValues
    coefficient0 alpha2 alpha value0 value1 value2 contribution0 contribution1
    contribution2 sum0 sum1 sum2 value0Run value1Run value2Run
    contribution0Run contribution1Run contribution2Run sum0Run sum1Run sum2Run
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeDone4, innerRun, half1Run, outRun]

private theorem firstPairOuterExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient0)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha2 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum2 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
        (rangeFrom 0#usize) (groupsFirstPair group0 group1 group2) groupValues
        (powers alpha alpha2 alpha3) unique0 coefficients0 unique0 slots0
        0#usize = ok out := by
  have step0 := firstPairOuterStep0 group0 group1 group2 groupValues alpha
    alpha2 alpha3
  have step1 := firstPairOuterStep1 group0 group1 group2 groupValues alpha
    alpha2 alpha3 coefficient0 coefficient0Run
  have step2 := firstPairOuterStep2 group0 group1 group2 different01 groupValues
    alpha alpha2 alpha3 coefficient0
  have step3 := firstPairOuterStep3 group0 group1 group2 different02 different12
    groupValues alpha alpha2 alpha3 coefficient0
  have done := firstPairOuterDone group0 group1 group2 groupValues alpha alpha2
    alpha3 coefficient0 value0 value1 value2 contribution0 contribution1
    contribution2 sum0 sum1 sum2 half1 out value0Run value1Run value2Run
    contribution0Run contribution1Run contribution2Run sum0Run sum1Run sum2Run
    half1Run outRun
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

theorem firstPairSourceExact
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 coefficient0 value0 value1 value2 contribution0
      contribution1 contribution2 sum0 sum1 sum2 half1 out : RawQM31)
    (coefficient0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 =
        ok coefficient0)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value0 coefficient0 = ok contribution0)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha2 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha = ok contribution2)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum2 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (groupsFirstPair group0 group1 group2) groupValues alpha alpha2 alpha3 =
      ok out := by
  have run := firstPairOuterExact group0 group1 group2 different01 different02
    different12 groupValues alpha alpha2 alpha3 coefficient0 value0 value1
    value2 contribution0 contribution1 contribution2 sum0 sum1 sum2 half1 out
    coefficient0Run value0Run value1Run value2Run contribution0Run
    contribution1Run contribution2Run sum0Run sum1Run sum2Run half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  simpa [rangeFrom, powers, unique0, coefficients0, slots0] using run

theorem firstPairSourceCorresponds
    (group0 group1 group2 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (groupValues : Slice RawQM31)
    (value0 value1 value2 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (value2Canonical : CanonicalQM31 value2)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (groupsFirstPair group0 group1 group2) groupValues alpha alpha2 alpha3 =
        ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value0,
            toMaintainedExact value1, toMaintainedExact value2] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
      oneCanonical alpha3Canonical
  obtain ⟨contribution0, contribution0Run, contribution0Canonical,
      contribution0Exact⟩ :=
    generated_qm31_mul_corresponds value0 coefficient0 value0Canonical
      coefficient0Canonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha2 value1Canonical
      alpha2Canonical
  obtain ⟨contribution2, contribution2Run, contribution2Canonical,
      contribution2Exact⟩ :=
    generated_qm31_mul_corresponds value2 alpha value2Canonical alphaCanonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO contribution0
      zeroCanonical contribution0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨sum2, sum2Run, sum2Canonical, sum2Exact⟩ :=
    generated_qm31_add_corresponds sum1 contribution2 sum1Canonical
      contribution2Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum2 sum2Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := firstPairSourceExact group0 group1 group2 different01
    different02 different12 groupValues alpha alpha2 alpha3 coefficient0
    value0 value1 value2 contribution0 contribution1 contribution2 sum0 sum1
    sum2 half1 out coefficient0Run value0Run value1Run value2Run
    contribution0Run contribution1Run contribution2Run sum0Run sum1Run sum2Run
    half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have coefficient0ExactM := congrArg oldQm31ToMaintained coefficient0Exact
  have contribution0ExactM := congrArg oldQm31ToMaintained contribution0Exact
  have contribution1ExactM := congrArg oldQm31ToMaintained contribution1Exact
  have contribution2ExactM := congrArg oldQm31ToMaintained contribution2Exact
  have sum0ExactM := congrArg oldQm31ToMaintained sum0Exact
  have sum1ExactM := congrArg oldQm31ToMaintained sum1Exact
  have sum2ExactM := congrArg oldQm31ToMaintained sum2Exact
  have half1ExactM := congrArg oldQm31ToMaintained half1Exact
  have outExactM := congrArg oldQm31ToMaintained outExact
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at coefficient0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution2ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum2ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at half1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at outExactM
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
    _ = toMaintainedExact sum2 := half1ExactM
    _ = toMaintainedExact sum1 + toMaintainedExact contribution2 := sum2ExactM
    _ = (toMaintainedExact sum0 + toMaintainedExact contribution1) +
        toMaintainedExact contribution2 := by rw [sum1ExactM]
    _ = ((toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
          toMaintainedExact contribution0) + toMaintainedExact contribution1) +
        toMaintainedExact contribution2 := by rw [sum0ExactM]
    _ = toMaintainedExact value0 * toMaintainedExact coefficient0 +
        toMaintainedExact value1 * toMaintainedExact alpha2 +
        toMaintainedExact value2 * toMaintainedExact alpha := by
      rw [zeroExact, contribution0ExactM, contribution1ExactM,
        contribution2ExactM]
      ring
    _ = toMaintainedExact value0 *
          ((1 : ExactQM31) + toMaintainedExact alpha ^ 3) +
        toMaintainedExact value1 * toMaintainedExact alpha ^ 2 +
        toMaintainedExact value2 * toMaintainedExact alpha := by
      rw [coefficient0ExactM, oneExact, alpha2Exact, alpha3Exact]
    _ = toMaintainedExact value0 +
        toMaintainedExact alpha ^ 3 * toMaintainedExact value0 +
        toMaintainedExact alpha ^ 2 * toMaintainedExact value1 +
        toMaintainedExact alpha * toMaintainedExact value2 := by ring

/-! ## The released `[3, 4, 5, 6]` tuple -/

def groupsAllDifferent
    (group0 group1 group2 group3 : Std.U8) : Array Std.U8 4#usize :=
  Array.make 4#usize [group0, group1, group2, group3]

private def allDifferentCoefficients
    (alpha alpha2 alpha3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE, alpha3, alpha2, alpha]

private def allDifferentCounts : Array Std.U8 4#usize :=
  Array.make 4#usize [1#u8, 1#u8, 1#u8, 1#u8]

private def allDifferentFirstSlots : Array Std.U8 4#usize :=
  Array.make 4#usize [0#u8, 1#u8, 2#u8, 3#u8]

private theorem allDifferentFindFourthStep0
    (group0 group1 group2 group3 : Std.U8) (different03 : group0 ≠ group3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (lastPairUnique3 group0 group1 group2) 3#usize group3 0#usize =
      ok (cont 1#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 0#usize =
        ok group0 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index0 group0 group1 group2 0#u8)
  have differentVal : group0.val ≠ group3.val := by
    intro same
    apply different03
    apply UScalar.val_eq_imp
    exact same
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, differentVal, usizeZeroSucc, Std.lift]

private theorem allDifferentFindFourthStep1
    (group0 group1 group2 group3 : Std.U8) (different13 : group1 ≠ group3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (lastPairUnique3 group0 group1 group2) 3#usize group3 1#usize =
      ok (cont 2#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 1#usize =
        ok group1 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index1 group0 group1 group2 0#u8)
  have differentVal : group1.val ≠ group3.val := by
    intro same
    apply different13
    apply UScalar.val_eq_imp
    exact same
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, differentVal, usizeOneSucc, Std.lift]

private theorem allDifferentFindFourthStep2
    (group0 group1 group2 group3 : Std.U8) (different23 : group2 ≠ group3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (lastPairUnique3 group0 group1 group2) 3#usize group3 2#usize =
      ok (cont 3#usize) := by
  have indexRun :
      Array.index_usize (lastPairUnique3 group0 group1 group2) 2#usize =
        ok group2 := by
    simpa [lastPairUnique3] using
      (arrayMake4Index2 group0 group1 group2 0#u8)
  have differentVal : group2.val ≠ group3.val := by
    intro same
    apply different23
    apply UScalar.val_eq_imp
    exact same
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    indexRun, differentVal, usizeTwoSucc, Std.lift]

private theorem allDifferentFindFourthDone
    (group0 group1 group2 group3 : Std.U8) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body
        (lastPairUnique3 group0 group1 group2) 3#usize group3 3#usize =
      ok (done 3#usize) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body]

private theorem allDifferentFindFourth
    (group0 group1 group2 group3 : Std.U8)
    (different03 : group0 ≠ group3) (different13 : group1 ≠ group3)
    (different23 : group2 ≠ group3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
        (lastPairUnique3 group0 group1 group2) 3#usize group3 0#usize =
      ok 3#usize := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1
  rw [loop.eq_1]
  rw [allDifferentFindFourthStep0 group0 group1 group2 group3 different03]
  simp only
  rw [loop.eq_1]
  rw [allDifferentFindFourthStep1 group0 group1 group2 group3 different13]
  simp only
  rw [loop.eq_1]
  rw [allDifferentFindFourthStep2 group0 group1 group2 group3 different23]
  simp only
  rw [loop.eq_1]
  rw [allDifferentFindFourthDone]

private theorem usizeThreeSucc :
    Std.Usize.wrapping_add 3#usize 1#usize = 4#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#usize).hSize; scalar_tac)]
  norm_num

private theorem allDifferentOuterStep0
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllDifferent group0 group1 group2 group3) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 0#usize) unique0 coefficients0
        unique0 slots0 0#usize =
      ok (cont (rangeFrom 1#usize, unique1 group0, coefficients1,
        countsAt 1#u8, slots0, 1#usize)) := by
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeNext0, allSameFindEmpty, groupsAllDifferent, powers, rangeFrom,
    unique0, unique1, coefficients0, coefficients1, countsAt, slots0,
    Array.index_usize, Array.update, UScalar.lt_equiv, Std.lift]
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

private theorem allDifferentOuterStep1
    (group0 group1 group2 group3 : Std.U8) (different01 : group0 ≠ group1)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllDifferent group0 group1 group2 group3) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 1#usize) (unique1 group0)
        coefficients1 (countsAt 1#u8) slots0 1#usize =
      ok (cont (rangeFrom 2#usize, oneThreeUnique2 group0 group1,
        threeAroundCoefficients11 alpha3, oneThreeCounts11,
        oneThreeFirstSlots, 2#usize)) := by
  have groupRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          1#usize = ok group1 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index1 group0 group1 group2 group3)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 1#usize =
      ok alpha3 := by
    simpa [powers] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext1, groupRun,
    oneThreeFindNew group0 group1 different01, powerRun]
  simp (config := { maxSteps := 100000 })
    [unique1, coefficients1, countsAt, slots0, oneThreeUnique2,
    threeAroundCoefficients11, oneThreeCounts11, oneThreeFirstSlots,
    Array.update, Std.lift, castUsizeOneU8, usizeOneSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem allDifferentOuterStep2
    (group0 group1 group2 group3 : Std.U8)
    (different02 : group0 ≠ group2) (different12 : group1 ≠ group2)
    (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllDifferent group0 group1 group2 group3) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 2#usize)
        (oneThreeUnique2 group0 group1) (threeAroundCoefficients11 alpha3)
        oneThreeCounts11 oneThreeFirstSlots 2#usize =
      ok (cont (rangeFrom 3#usize, lastPairUnique3 group0 group1 group2,
        lastPairCoefficients111 alpha3 alpha2, lastPairCounts111,
        lastPairFirstSlots, 3#usize)) := by
  have groupRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          2#usize = ok group2 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index2 group0 group1 group2 group3)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 2#usize =
      ok alpha2 := by
    simpa [powers] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext2, groupRun,
    lastPairFindNew group0 group1 group2 different02 different12, powerRun]
  simp (config := { maxSteps := 100000 })
    [oneThreeUnique2, threeAroundCoefficients11, oneThreeCounts11,
    oneThreeFirstSlots, lastPairUnique3, lastPairCoefficients111,
    lastPairCounts111, lastPairFirstSlots, Array.update, Std.lift,
    castUsizeTwoU8, usizeTwoSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem allDifferentOuterStep3
    (group0 group1 group2 group3 : Std.U8)
    (different03 : group0 ≠ group3) (different13 : group1 ≠ group3)
    (different23 : group2 ≠ group3) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllDifferent group0 group1 group2 group3) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 3#usize)
        (lastPairUnique3 group0 group1 group2)
        (lastPairCoefficients111 alpha3 alpha2) lastPairCounts111
        lastPairFirstSlots 3#usize =
      ok (cont (rangeFrom 4#usize,
        groupsAllDifferent group0 group1 group2 group3,
        allDifferentCoefficients alpha alpha2 alpha3, allDifferentCounts,
        allDifferentFirstSlots, 4#usize)) := by
  have groupRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          3#usize = ok group3 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index3 group0 group1 group2 group3)
  have powerRun : Array.index_usize (powers alpha alpha2 alpha3) 3#usize =
      ok alpha := by
    simpa [powers] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
        alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeNext3, groupRun,
    allDifferentFindFourth group0 group1 group2 group3 different03 different13
      different23,
    powerRun]
  simp (config := { maxSteps := 100000 })
    [lastPairUnique3, lastPairCoefficients111, lastPairCounts111,
    lastPairFirstSlots, groupsAllDifferent, allDifferentCoefficients,
    allDifferentCounts, allDifferentFirstSlots, Array.update, Std.lift,
    castUsizeThreeU8, usizeThreeSucc]
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  constructor
  · apply Subtype.ext
    rfl
  · rfl

private theorem allDifferentInnerStep0
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value0 sum0 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 0#usize, «end» := 4#usize }
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok (cont ({ start := 1#usize, «end» := 4#usize }, sum0)) := by
  have uniqueRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          0#usize = ok group0 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index0 group0 group1 group2 group3)
  have firstSlotRun :
      Array.index_usize allDifferentFirstSlots 0#usize = ok 0#u8 := by
    simpa [allDifferentFirstSlots] using
      (arrayMake4Index0 0#u8 1#u8 2#u8 3#u8)
  have countRun : Array.index_usize allDifferentCounts 0#usize = ok 1#u8 := by
    simpa [allDifferentCounts] using
      (arrayMake4Index0 1#u8 1#u8 1#u8 1#u8)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext0, uniqueRun, fromU8ToUsizeExact, value0Run, firstSlotRun,
    countRun, sum0Run, Std.lift]

private theorem allDifferentInnerStep1
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value1 contribution1 sum0 sum1 : RawQM31)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 1#usize, «end» := 4#usize } sum0 =
      ok (cont ({ start := 2#usize, «end» := 4#usize }, sum1)) := by
  have uniqueRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          1#usize = ok group1 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index1 group0 group1 group2 group3)
  have firstSlotRun :
      Array.index_usize allDifferentFirstSlots 1#usize = ok 1#u8 := by
    simpa [allDifferentFirstSlots] using
      (arrayMake4Index1 0#u8 1#u8 2#u8 3#u8)
  have coefficientRun :
      Array.index_usize (allDifferentCoefficients alpha alpha2 alpha3)
          1#usize = ok alpha3 := by
    simpa [allDifferentCoefficients] using
      (arrayMake4Index1
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext1, uniqueRun, fromU8ToUsizeExact, value1Run, firstSlotRun,
    coefficientRun, contribution1Run, sum1Run, Std.lift]

private theorem allDifferentInnerStep2
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value2 contribution2 sum1 sum2 : RawQM31)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha2 = ok contribution2)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 2#usize, «end» := 4#usize } sum1 =
      ok (cont ({ start := 3#usize, «end» := 4#usize }, sum2)) := by
  have uniqueRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          2#usize = ok group2 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index2 group0 group1 group2 group3)
  have firstSlotRun :
      Array.index_usize allDifferentFirstSlots 2#usize = ok 2#u8 := by
    simpa [allDifferentFirstSlots] using
      (arrayMake4Index2 0#u8 1#u8 2#u8 3#u8)
  have coefficientRun :
      Array.index_usize (allDifferentCoefficients alpha alpha2 alpha3)
          2#usize = ok alpha2 := by
    simpa [allDifferentCoefficients] using
      (arrayMake4Index2
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext2, uniqueRun, fromU8ToUsizeExact, value2Run, firstSlotRun,
    coefficientRun, contribution2Run, sum2Run, Std.lift]

private theorem allDifferentInnerStep3
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value3 contribution3 sum2 sum3 : RawQM31)
    (value3Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (contribution3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value3 alpha = ok contribution3)
    (sum3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum2 contribution3 =
        ok sum3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 3#usize, «end» := 4#usize } sum2 =
      ok (cont ({ start := 4#usize, «end» := 4#usize }, sum3)) := by
  have uniqueRun :
      Array.index_usize (groupsAllDifferent group0 group1 group2 group3)
          3#usize = ok group3 := by
    simpa [groupsAllDifferent] using
      (arrayMake4Index3 group0 group1 group2 group3)
  have firstSlotRun :
      Array.index_usize allDifferentFirstSlots 3#usize = ok 3#u8 := by
    simpa [allDifferentFirstSlots] using
      (arrayMake4Index3 0#u8 1#u8 2#u8 3#u8)
  have coefficientRun :
      Array.index_usize (allDifferentCoefficients alpha alpha2 alpha3)
          3#usize = ok alpha := by
    simpa [allDifferentCoefficients] using
      (arrayMake4Index3
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3 alpha2 alpha)
  simp (config := { maxSteps := 100000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeNext3, uniqueRun, fromU8ToUsizeExact, value3Run, firstSlotRun,
    coefficientRun, contribution3Run, sum3Run, Std.lift]

private theorem allDifferentInnerDone
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 sum3 : RawQM31) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body
        groupValues (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots { start := 4#usize, «end» := 4#usize } sum3 =
      ok (done sum3) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    rangeDone4]

private theorem allDifferentInnerExact
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value0 value1 value2 value3 contribution1
      contribution2 contribution3 sum0 sum1 sum2 sum3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value3Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha2 = ok contribution2)
    (contribution3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value3 alpha = ok contribution3)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (sum3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum2 contribution3 =
        ok sum3) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
        { start := 0#usize, «end» := 4#usize } groupValues
        (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO =
      ok sum3 := by
  have step0 := allDifferentInnerStep0 group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 value0 sum0 value0Run sum0Run
  have step1 := allDifferentInnerStep1 group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 value1 contribution1 sum0 sum1 value1Run
    contribution1Run sum1Run
  have step2 := allDifferentInnerStep2 group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 value2 contribution2 sum1 sum2 value2Run
    contribution2Run sum2Run
  have step3 := allDifferentInnerStep3 group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 value3 contribution3 sum2 sum3 value3Run
    contribution3Run sum3Run
  have done := allDifferentInnerDone group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 sum3
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0
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

private theorem allDifferentOuterDone
    (group0 group1 group2 group3 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value0 value1 value2 value3 contribution1
      contribution2 contribution3 sum0 sum1 sum2 sum3 half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value3Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha2 = ok contribution2)
    (contribution3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value3 alpha = ok contribution3)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (sum3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum2 contribution3 =
        ok sum3)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum3 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body
        (groupsAllDifferent group0 group1 group2 group3) groupValues
        (powers alpha alpha2 alpha3) (rangeFrom 4#usize)
        (groupsAllDifferent group0 group1 group2 group3)
        (allDifferentCoefficients alpha alpha2 alpha3) allDifferentCounts
        allDifferentFirstSlots 4#usize = ok (done out) := by
  have innerRun := allDifferentInnerExact group0 group1 group2 group3
    groupValues alpha alpha2 alpha3 value0 value1 value2 value3 contribution1
    contribution2 contribution3 sum0 sum1 sum2 sum3 value0Run value1Run
    value2Run value3Run contribution1Run contribution2Run contribution3Run
    sum0Run sum1Run sum2Run sum3Run
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    rangeFrom, rangeDone4, innerRun, half1Run, outRun]

private theorem allDifferentOuterExact
    (group0 group1 group2 group3 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (different03 : group0 ≠ group3)
    (different13 : group1 ≠ group3) (different23 : group2 ≠ group3)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value0 value1 value2 value3 contribution1
      contribution2 contribution3 sum0 sum1 sum2 sum3 half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value3Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha2 = ok contribution2)
    (contribution3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value3 alpha = ok contribution3)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (sum3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum2 contribution3 =
        ok sum3)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum3 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0
        (rangeFrom 0#usize) (groupsAllDifferent group0 group1 group2 group3)
        groupValues (powers alpha alpha2 alpha3) unique0 coefficients0 unique0
        slots0 0#usize = ok out := by
  have step0 := allDifferentOuterStep0 group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3
  have step1 := allDifferentOuterStep1 group0 group1 group2 group3 different01
    groupValues alpha alpha2 alpha3
  have step2 := allDifferentOuterStep2 group0 group1 group2 group3 different02
    different12 groupValues alpha alpha2 alpha3
  have step3 := allDifferentOuterStep3 group0 group1 group2 group3 different03
    different13 different23 groupValues alpha alpha2 alpha3
  have done := allDifferentOuterDone group0 group1 group2 group3 groupValues
    alpha alpha2 alpha3 value0 value1 value2 value3 contribution1 contribution2
    contribution3 sum0 sum1 sum2 sum3 half1 out value0Run value1Run value2Run
    value3Run contribution1Run contribution2Run contribution3Run sum0Run sum1Run
    sum2Run sum3Run half1Run outRun
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

theorem allDifferentSourceExact
    (group0 group1 group2 group3 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (different03 : group0 ≠ group3)
    (different13 : group1 ≠ group3) (different23 : group2 ≠ group3)
    (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 value0 value1 value2 value3 contribution1
      contribution2 contribution3 sum0 sum1 sum2 sum3 half1 out : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value3Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (contribution1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value1 alpha3 = ok contribution1)
    (contribution2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value2 alpha2 = ok contribution2)
    (contribution3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul
          value3 alpha = ok contribution3)
    (sum0Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0 =
        ok sum0)
    (sum1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 contribution1 =
        ok sum1)
    (sum2Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum1 contribution2 =
        ok sum2)
    (sum3Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.add sum2 contribution3 =
        ok sum3)
    (half1Run :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half sum3 = ok half1)
    (outRun :
      V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok out) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (groupsAllDifferent group0 group1 group2 group3) groupValues alpha alpha2
        alpha3 = ok out := by
  have run := allDifferentOuterExact group0 group1 group2 group3 different01
    different02 different12 different03 different13 different23 groupValues
    alpha alpha2 alpha3 value0 value1 value2 value3 contribution1 contribution2
    contribution3 sum0 sum1 sum2 sum3 half1 out value0Run value1Run value2Run
    value3Run contribution1Run contribution2Run contribution3Run sum0Run sum1Run
    sum2Run sum3Run half1Run outRun
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
  simpa [rangeFrom, powers, unique0, coefficients0, slots0] using run

theorem allDifferentSourceCorresponds
    (group0 group1 group2 group3 : Std.U8)
    (different01 : group0 ≠ group1) (different02 : group0 ≠ group2)
    (different12 : group1 ≠ group2) (different03 : group0 ≠ group3)
    (different13 : group1 ≠ group3) (different23 : group2 ≠ group3)
    (groupValues : Slice RawQM31)
    (value0 value1 value2 value3 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value2Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group2) = ok value2)
    (value3Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group3) = ok value3)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (value2Canonical : CanonicalQM31 value2)
    (value3Canonical : CanonicalQM31 value3)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (groupsAllDifferent group0 group1 group2 group3) groupValues alpha
          alpha2 alpha3 = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value1,
            toMaintainedExact value2, toMaintainedExact value3] index) := by
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    generated_qm31_mul_corresponds value1 alpha3 value1Canonical
      alpha3Canonical
  obtain ⟨contribution2, contribution2Run, contribution2Canonical,
      contribution2Exact⟩ :=
    generated_qm31_mul_corresponds value2 alpha2 value2Canonical
      alpha2Canonical
  obtain ⟨contribution3, contribution3Run, contribution3Canonical,
      contribution3Exact⟩ :=
    generated_qm31_mul_corresponds value3 alpha value3Canonical alphaCanonical
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO value0
      zeroCanonical value0Canonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    generated_qm31_add_corresponds sum0 contribution1 sum0Canonical
      contribution1Canonical
  obtain ⟨sum2, sum2Run, sum2Canonical, sum2Exact⟩ :=
    generated_qm31_add_corresponds sum1 contribution2 sum1Canonical
      contribution2Canonical
  obtain ⟨sum3, sum3Run, sum3Canonical, sum3Exact⟩ :=
    generated_qm31_add_corresponds sum2 contribution3 sum2Canonical
      contribution3Canonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    generated_qm31_half_corresponds sum3 sum3Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_half_corresponds half1 half1Canonical
  have sourceRun := allDifferentSourceExact group0 group1 group2 group3
    different01 different02 different12 different03 different13 different23
    groupValues alpha alpha2 alpha3 value0 value1 value2 value3 contribution1
    contribution2 contribution3 sum0 sum1 sum2 sum3 half1 out value0Run
    value1Run value2Run value3Run contribution1Run contribution2Run
    contribution3Run sum0Run sum1Run sum2Run sum3Run half1Run outRun
  refine ⟨out, sourceRun, outCanonical, ?_⟩
  have contribution1ExactM := congrArg oldQm31ToMaintained contribution1Exact
  have contribution2ExactM := congrArg oldQm31ToMaintained contribution2Exact
  have contribution3ExactM := congrArg oldQm31ToMaintained contribution3Exact
  have sum0ExactM := congrArg oldQm31ToMaintained sum0Exact
  have sum1ExactM := congrArg oldQm31ToMaintained sum1Exact
  have sum2ExactM := congrArg oldQm31ToMaintained sum2Exact
  have sum3ExactM := congrArg oldQm31ToMaintained sum3Exact
  have half1ExactM := congrArg oldQm31ToMaintained half1Exact
  have outExactM := congrArg oldQm31ToMaintained outExact
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution2ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_mul] at contribution3ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum0ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum2ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at sum3ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at half1ExactM
  simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add] at outExactM
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
    _ = toMaintainedExact sum3 := half1ExactM
    _ = toMaintainedExact sum2 + toMaintainedExact contribution3 := sum3ExactM
    _ = (toMaintainedExact sum1 + toMaintainedExact contribution2) +
        toMaintainedExact contribution3 := by rw [sum2ExactM]
    _ = ((toMaintainedExact sum0 + toMaintainedExact contribution1) +
        toMaintainedExact contribution2) + toMaintainedExact contribution3 := by
      rw [sum1ExactM]
    _ = (((toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
          toMaintainedExact value0) + toMaintainedExact contribution1) +
        toMaintainedExact contribution2) + toMaintainedExact contribution3 := by
      rw [sum0ExactM]
    _ = toMaintainedExact value0 +
        toMaintainedExact value1 * toMaintainedExact alpha3 +
        toMaintainedExact value2 * toMaintainedExact alpha2 +
        toMaintainedExact value3 * toMaintainedExact alpha := by
      rw [zeroExact, contribution1ExactM, contribution2ExactM,
        contribution3ExactM]
      ring
    _ = toMaintainedExact value0 +
        toMaintainedExact value1 * toMaintainedExact alpha ^ 3 +
        toMaintainedExact value2 * toMaintainedExact alpha ^ 2 +
        toMaintainedExact value3 * toMaintainedExact alpha := by
      rw [alpha2Exact, alpha3Exact]
    _ = toMaintainedExact value0 +
        toMaintainedExact alpha ^ 3 * toMaintainedExact value1 +
        toMaintainedExact alpha ^ 2 * toMaintainedExact value2 +
        toMaintainedExact alpha * toMaintainedExact value3 := by ring

end AspisV5RelationLinkedGroupTuple
