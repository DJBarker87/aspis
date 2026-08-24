import V5RelationLinkedGroupedRows
import V5AcceptedInactiveMaskFormulas

/-!
# Exact initial semantics of the released inactive table

The fourth prepared relation component stores a 1024-entry binary covector as
64 row-group identifiers and seven 16-bit masks.  This file gives that compact
state a direct maintained-field meaning and connects the first two deferred
folds to the already proved seven-value source trace.
-/

namespace AspisV5AcceptedInactiveInitialSemantics

open Aeneas Aeneas.Std Result
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedGroupedFold
open AspisV5RelationLinkedGroupedRows
open AspisV5RelationLinkedGroupedLowSemantics
open AspisV5AcceptedInactiveMaskFormulas

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 :=
  ⟨V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO⟩

/-- Mathematical function represented by the released compact row/group
layout.  It is repeated here so the initial-table theorem has no dependency
on the later grouped-row source proof. -/
def representedReleasedGroupedWeights {n : Nat}
    (rowGroups : alloc.vec.Vec Std.U8) (groupValues : alloc.vec.Vec RawQM31) :
    Fin n → ExactQM31 :=
  fun index =>
    toMaintainedExact
      groupValues.val[(rowGroups.val[index.val]!).val]!

/-- The unfurled 1024-entry covector represented by the exact released row
groups and masks.  Division by 16 selects the row and remainder selects its
least-significant-bit-first mask position. -/
def releasedInactiveInitialWeight (index : Fin 1024) : ExactQM31 :=
  let high : Fin 64 := ⟨index.val / 16, by omega⟩
  let low : Fin 16 := ⟨index.val % 16, Nat.mod_lt _ (by decide)⟩
  let group := (releasedRowGroups64.val[high.val]!).val
  let mask := (releasedMasks.val[group]!).val
  maskBitWeight mask low

/-- Every released row byte is one of the seven released mask indices. -/
def releasedRowGroupIndex (row : Fin 64) : Fin 7 :=
  ⟨(releasedRowGroups64.val[row.val]!).val, by
    fin_cases row <;> simp [releasedRowGroups64]⟩

/-- Each of the seven values actually returned by the extracted Rust low-mask
fold is the exact two-fold value of its released 16-bit mask.  This cancels
the four source `half` calls; it does not introduce division as an assumption. -/
theorem releasedLowValue_eq_foldMaskTwice
    (alpha0 alpha1 : RawQM31)
    (power : ReleasedBinaryPowerTrace alpha0 alpha1)
    (values : ReleasedMaskValuesTrace
      (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0 power.cross
        alpha1) power.total)
    (semantics : ReleasedLowValuesSemantics alpha0 alpha1 power values)
    (group : Fin 7) :
    toMaintainedExact
        (releasedLowSevenValues
          values.trace0.value values.trace1.value values.trace2.value
          values.trace3.value values.trace4.value values.trace5.value
          values.trace6.value).val[group.val]! =
      foldMaskTwice (toMaintainedExact alpha0) (toMaintainedExact alpha1)
        (releasedMasks.val[group.val]!).val := by
  apply mul_left_cancel₀ sixteen_ne_zero
  calc
    (16 : ExactQM31) * toMaintainedExact
        (releasedLowSevenValues
          values.trace0.value values.trace1.value values.trace2.value
          values.trace3.value values.trace4.value values.trace5.value
          values.trace6.value).val[group.val]! =
      releasedLowNumerator (toMaintainedExact alpha0)
        (toMaintainedExact alpha1) group := by
      fin_cases group
      · simpa [releasedLowSevenValues] using semantics.exact0
      · simpa [releasedLowSevenValues] using semantics.exact1
      · simpa [releasedLowSevenValues] using semantics.exact2
      · simpa [releasedLowSevenValues] using semantics.exact3
      · simpa [releasedLowSevenValues] using semantics.exact4
      · simpa [releasedLowSevenValues] using semantics.exact5
      · simpa [releasedLowSevenValues] using semantics.exact6
    _ = (16 : ExactQM31) *
        foldMaskTwice (toMaintainedExact alpha0) (toMaintainedExact alpha1)
          (releasedMasks.val[group.val]!).val :=
      (sixteen_foldMaskTwice_eq_releasedLowNumerator
        (toMaintainedExact alpha0) (toMaintainedExact alpha1) group).symm

/-- Folding the unfurled 1024-entry table twice is, row by row, the two-fold
value of that row's exact released mask. -/
theorem releasedInactiveInitialWeight_fold_twice_at_row
    (alpha0 alpha1 : ExactQM31) (row : Fin 64) :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64 alpha1
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 256 alpha0
          releasedInactiveInitialWeight) row =
      foldMaskTwice alpha0 alpha1
        (releasedMasks.val[(releasedRowGroupIndex row).val]!).val := by
  simp only [AspisV5FriRelationCandidateBridge.dualWeightFoldLayer,
    foldMaskTwice]
  congr 1
  funext outer
  congr 1
  funext inner
  simp [releasedInactiveInitialWeight, releasedRowGroupIndex,
    AspisV5ComponentCConcreteFoldLinearity.childIndex]
  congr <;> omega

/-- The seven-value compact state produced by the extracted Rust low-mask
fold represents exactly the result of folding the fixed 1024-entry inactive
table by the first two challenges. -/
theorem releasedLowValues_represent_foldedInactiveInitialWeight
    (alpha0 alpha1 : RawQM31)
    (power : ReleasedBinaryPowerTrace alpha0 alpha1)
    (values : ReleasedMaskValuesTrace
      (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0 power.cross
        alpha1) power.total)
    (semantics : ReleasedLowValuesSemantics alpha0 alpha1 power values) :
    representedReleasedGroupedWeights releasedRowGroups64
        (releasedLowSevenValues
          values.trace0.value values.trace1.value values.trace2.value
          values.trace3.value values.trace4.value values.trace5.value
          values.trace6.value) =
      AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64
        (toMaintainedExact alpha1)
        (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 256
          (toMaintainedExact alpha0) releasedInactiveInitialWeight) := by
  funext row
  rw [releasedInactiveInitialWeight_fold_twice_at_row]
  simpa [representedReleasedGroupedWeights, releasedRowGroupIndex] using
    releasedLowValue_eq_foldMaskTwice alpha0 alpha1 power values semantics
      (releasedRowGroupIndex row)

#print axioms sixteen_foldMaskTwice_eq_releasedLowNumerator
#print axioms releasedLowValue_eq_foldMaskTwice
#print axioms releasedInactiveInitialWeight_fold_twice_at_row
#print axioms releasedLowValues_represent_foldedInactiveInitialWeight

end AspisV5AcceptedInactiveInitialSemantics
