import V5RelationLinkedGroupTuple
import V5RelationLinkedGroupedRowsStaged

/-!
# Exact semantics of the two released grouped-row folds

The deferred binary relation component represents a 1024-entry binary table
by sixty-four row-group identifiers and seven group values.  After the two
low-coordinate folds, the production Rust performs two calls to
`fold_grouped_rows`, first for the fixed 64-row table and then for the fixed
16-row table.

This file proves that those two *source-extracted* calls are exactly the
maintained four-way dual-weight fold.  It is deliberately fixed to the row
tables in the release: there is no invented inverse, arbitrary schedule, or
universal claim about unsupported group layouts.
-/

namespace AspisV5RelationLinkedGroupedRowsSemantics

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedGroupTuple
open AspisV5RelationLinkedGroupedRows
open AspisV5RelationLinkedGroupedRowsStaged

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

abbrev releasedSevenValues :=
  AspisV5RelationLinkedGroupedRowsStaged.releasedSevenValuesStaged

local instance : Inhabited RawQM31 :=
  ⟨V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO⟩

@[simp] private theorem castU8ToUsizeVal (value : Std.U8) :
    (UScalar.cast .Usize value).val = value.val := by
  rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
  have h := value.hBounds
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [UScalarTy.numBits, hbits] at h ⊢ <;> omega

/-- Mathematical function represented by a row-group vector and group-value
vector.  The total `get!` form mirrors the source representation; the release
theorems below reduce every access to one of the explicit in-bounds entries. -/
def representedGroupedWeights {n : Nat}
    (rowGroups : alloc.vec.Vec Std.U8) (groupValues : alloc.vec.Vec RawQM31) :
    Fin n → ExactQM31 :=
  fun index =>
    toMaintainedExact
      groupValues.val[(rowGroups.val[index.val]!).val]!

def CanonicalSeven
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31) : Prop :=
  CanonicalQM31 value0 ∧ CanonicalQM31 value1 ∧ CanonicalQM31 value2 ∧
    CanonicalQM31 value3 ∧ CanonicalQM31 value4 ∧ CanonicalQM31 value5 ∧
    CanonicalQM31 value6

def CanonicalFour (value0 value1 value2 value3 : RawQM31) : Prop :=
  CanonicalQM31 value0 ∧ CanonicalQM31 value1 ∧ CanonicalQM31 value2 ∧
    CanonicalQM31 value3

/-- The actual first released grouped-row call (64 rows to 16 rows) computes
one maintained dual fold at every output position. -/
theorem released_first_grouped_rows_corresponds
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (hvalues : CanonicalSeven value0 value1 value2 value3 value4 value5 value6)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (halpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (halpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out0 out1 out2 out3 out4 out5 out6,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
          (alloc.vec.Vec.deref releasedRowGroups64)
          (alloc.vec.Vec.deref
            (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))
          alpha alpha2 alpha3 =
        ok (releasedRowGroups16,
          releasedSevenValues out0 out1 out2 out3 out4 out5 out6) ∧
      CanonicalSeven out0 out1 out2 out3 out4 out5 out6 ∧
      representedGroupedWeights releasedRowGroups16
          (releasedSevenValues out0 out1 out2 out3 out4 out5 out6) =
        AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 16
          (toMaintainedExact alpha)
          (representedGroupedWeights releasedRowGroups64
            (releasedSevenValues value0 value1 value2 value3 value4 value5 value6)) := by
  rcases hvalues with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  let values := releasedSevenValues value0 value1 value2 value3 value4 value5 value6
  have read0 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 0#u8) = ok value0 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read1 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 1#u8) = ok value1 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read2 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 2#u8) = ok value2 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read3 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 3#u8) = ok value3 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read4 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 4#u8) = ok value4 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read5 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 5#u8) = ok value5 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read6 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 6#u8) = ok value6 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  obtain ⟨out0, run0, hout0, exact0⟩ :=
    pairPairSourceCorresponds (alloc.vec.Vec.deref values)
      value0 value1 alpha alpha2 alpha3 read0 read1 h0 h1 halpha halpha2 halpha3
      halpha2Exact halpha3Exact
  obtain ⟨out1, run1, hout1, exact1⟩ :=
    allSameSourceCorresponds 1#u8 (alloc.vec.Vec.deref values)
      value1 alpha alpha2 alpha3 read1 h1 halpha halpha2
      halpha3 halpha2Exact halpha3Exact
  obtain ⟨out2, run2, hout2, exact2⟩ :=
    tripleFirstSourceCorresponds (alloc.vec.Vec.deref values)
      value1 value2 alpha alpha2 alpha3 read1 read2 h1 h2 halpha halpha2 halpha3
      halpha2Exact halpha3Exact
  obtain ⟨out3, run3, hout3, exact3⟩ :=
    splitPairSourceCorresponds 0#u8 2#u8 1#u8 (by decide) (by decide)
      (by decide) (alloc.vec.Vec.deref values) value0 value2 value1
      alpha alpha2 alpha3 read0 read2 read1 h0 h2 h1 halpha halpha2 halpha3
      halpha2Exact halpha3Exact
  obtain ⟨out4, run4, hout4, exact4⟩ :=
    oneThreeSourceCorresponds 1#u8 3#u8 (by decide)
      (alloc.vec.Vec.deref values) value1 value3 alpha alpha2 alpha3
      read1 read3 h1 h3 halpha halpha2
      halpha3 halpha2Exact halpha3Exact
  obtain ⟨out5, run5, hout5, exact5⟩ :=
    allDifferentSourceCorresponds 3#u8 4#u8 5#u8 6#u8
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (alloc.vec.Vec.deref values) value3 value4 value5 value6
      alpha alpha2 alpha3 read3 read4 read5 read6 h3 h4 h5 h6
      halpha halpha2 halpha3 halpha2Exact halpha3Exact
  obtain ⟨out6, run6, hout6, exact6⟩ :=
    allSameSourceCorresponds 6#u8 (alloc.vec.Vec.deref values)
      value6 alpha alpha2 alpha3 read6 h6 halpha halpha2
      halpha3 halpha2Exact halpha3Exact
  refine ⟨out0, out1, out2, out3, out4, out5, out6, ?_,
    ⟨hout0, hout1, hout2, hout3, hout4, hout5, hout6⟩, ?_⟩
  · simpa [values, groupsPairPair, groupsTripleFirst, groupsSplitPair,
      groupsOneThree, groupsAllDifferent, groupsAllSame] using
      released_first_grouped_rows_source_wire_exact
        (alloc.vec.Vec.deref values) alpha alpha2 alpha3
        out0 out1 out2 out3 out4 out5 out6 run0 run1 run2 run3 run4 run5 run6
  · funext index
    fin_cases index <;>
      simp [representedGroupedWeights, releasedRowGroups64, releasedRowGroups16,
        releasedSevenValues, releasedSevenValuesStaged,
        AspisV5FriRelationCandidateBridge.dualWeightFoldLayer,
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue,
        AspisV5ComponentCConcreteFoldLinearity.childIndex,
        exact0, exact1, exact2, exact3, exact4, exact5, exact6]

/-- The actual second released grouped-row call (16 rows to 4 rows) computes
one maintained dual fold at every output position. -/
theorem released_second_grouped_rows_corresponds
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (hvalues : CanonicalSeven value0 value1 value2 value3 value4 value5 value6)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (halpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (halpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out0 out1 out2 out3,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_grouped_rows
          (alloc.vec.Vec.deref releasedRowGroups16)
          (alloc.vec.Vec.deref
            (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))
          alpha alpha2 alpha3 =
        ok (releasedRowGroups4, releasedFourValues out0 out1 out2 out3) ∧
      CanonicalFour out0 out1 out2 out3 ∧
      representedGroupedWeights releasedRowGroups4
          (releasedFourValues out0 out1 out2 out3) =
        AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 4
          (toMaintainedExact alpha)
          (representedGroupedWeights releasedRowGroups16
            (releasedSevenValues value0 value1 value2 value3 value4 value5 value6)) := by
  rcases hvalues with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  let values := releasedSevenValues value0 value1 value2 value3 value4 value5 value6
  have read0 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 0#u8) = ok value0 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read1 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 1#u8) = ok value1 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read2 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 2#u8) = ok value2 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read3 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 3#u8) = ok value3 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read4 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 4#u8) = ok value4 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read5 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 5#u8) = ok value5 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  have read6 : Slice.index_usize (alloc.vec.Vec.deref values)
      (UScalar.cast .Usize 6#u8) = ok value6 := by
    simp [values, releasedSevenValues, releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize, castU8ToUsizeVal]
  obtain ⟨out0, run0, hout0, exact0⟩ :=
    oneThreeSourceCorresponds 0#u8 1#u8 (by decide)
      (alloc.vec.Vec.deref values) value0 value1 alpha alpha2 alpha3
      read0 read1 h0 h1 halpha halpha2
      halpha3 halpha2Exact halpha3Exact
  obtain ⟨out1, run1, hout1, exact1⟩ :=
    threeAroundSourceCorresponds 1#u8 2#u8 (by decide)
      (alloc.vec.Vec.deref values) value1 value2 alpha alpha2 alpha3
      read1 read2 h1 h2 halpha halpha2
      halpha3 halpha2Exact halpha3Exact
  obtain ⟨out2, run2, hout2, exact2⟩ :=
    firstPairSourceCorresponds 1#u8 2#u8 3#u8 (by decide) (by decide)
      (by decide) (alloc.vec.Vec.deref values) value1 value2 value3
      alpha alpha2 alpha3 read1 read2 read3 h1 h2 h3 halpha halpha2 halpha3
      halpha2Exact halpha3Exact
  obtain ⟨out3, run3, hout3, exact3⟩ :=
    lastPairSourceCorresponds 4#u8 5#u8 6#u8 (by decide) (by decide)
      (by decide) (alloc.vec.Vec.deref values) value4 value5 value6
      alpha alpha2 alpha3 read4 read5 read6 h4 h5 h6 halpha halpha2 halpha3
      halpha2Exact halpha3Exact
  refine ⟨out0, out1, out2, out3, ?_, ⟨hout0, hout1, hout2, hout3⟩, ?_⟩
  · simpa [values, groupsOneThree, groupsThreeAround, groupsFirstPair,
      groupsLastPair] using
      released_second_grouped_rows_source_wire_exact
        (alloc.vec.Vec.deref values) alpha alpha2 alpha3
        out0 out1 out2 out3 run0 run1 run2 run3
  · funext index
    fin_cases index <;>
      simp [representedGroupedWeights, releasedRowGroups16, releasedRowGroups4,
        releasedSevenValues, releasedSevenValuesStaged, releasedFourValues,
        AspisV5FriRelationCandidateBridge.dualWeightFoldLayer,
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue,
        AspisV5ComponentCConcreteFoldLinearity.childIndex,
        exact0, exact1, exact2, exact3]

#print axioms released_first_grouped_rows_corresponds
#print axioms released_second_grouped_rows_corresponds

end AspisV5RelationLinkedGroupedRowsSemantics
