import V5AcceptedStructuredWeightSemantics

/-!
# Structured cells across the accepted four-round accumulator

Every relation round appends two tensor cells and then folds every retained
cell.  This file packages the common list-preservation and one-to-four-fold
journeys.  The proofs use only the exact accepted fold result and the exact
append shape; they do not assume a second execution of either operation.
-/

namespace AspisV5AcceptedStructuredWeightJourneys

open Aeneas Aeneas.Std Result
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriRelationCandidateBridge
open AspisV5RelationFullLinkedAccumulatorBridge
open AspisV5RelationLinkedFieldProjection
open AspisV5AcceptedStructuredWeightSemantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev FullComponent :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightComponent
abbrev FullWeights :=
  V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator

/-- Appending later tensor cells leaves an existing structured cell at the
same list index with exactly the same mathematical meaning. -/
def StructuredCellAt.append
    {kind : StructuredWeightKind} {weights output : FullWeights}
    {target rounds : Nat}
    (cell : StructuredCellAt kind weights target rounds)
    (targetBound : target < weights.components.val.length)
    (suffix : List FullComponent)
    (shape : output.components.val = weights.components.val ++ suffix) :
    StructuredCellAt kind output target rounds := by
  refine {
    scale := cell.scale
    values := cell.values
    cell := ?_
    scaleCanonical := cell.scaleCanonical
    valuesCanonical := cell.valuesCanonical
    valuesLength := cell.valuesLength }
  rw [shape, List.getElem!_append_left _ suffix target targetBound]
  exact cell.cell

/-- Four maintained arity-four folds, from 1024 entries to four. -/
def foldFourMeaning (alpha0 alpha1 alpha2 alpha3 : ExactQM31)
    (weights : Fin 1024 → ExactQM31) : Fin 4 → ExactQM31 :=
  dualWeightFoldLayer 4 alpha3
    (dualWeightFoldLayer 16 alpha2
      (dualWeightFoldLayer 64 alpha1
        (dualWeightFoldLayer 256 alpha0 weights)))

/-- The final three maintained folds, from 256 entries to four. -/
def foldThreeMeaning (alpha1 alpha2 alpha3 : ExactQM31)
    (weights : Fin 256 → ExactQM31) : Fin 4 → ExactQM31 :=
  dualWeightFoldLayer 4 alpha3
    (dualWeightFoldLayer 16 alpha2
      (dualWeightFoldLayer 64 alpha1 weights))

/-- The final two maintained folds, from 64 entries to four. -/
def foldTwoMeaning (alpha2 alpha3 : ExactQM31)
    (weights : Fin 64 → ExactQM31) : Fin 4 → ExactQM31 :=
  dualWeightFoldLayer 4 alpha3
    (dualWeightFoldLayer 16 alpha2 weights)

/-- One maintained final fold, from sixteen entries to four. -/
def foldOneMeaning (alpha3 : ExactQM31)
    (weights : Fin 16 → ExactQM31) : Fin 4 → ExactQM31 :=
  dualWeightFoldLayer 4 alpha3 weights

/-- A structured cell present before round zero follows the same index
through every append and all four successful production folds. -/
theorem StructuredCellAt.foldFour
    {kind : StructuredWeightKind}
    {pre0 weights1 pre1 weights2 pre2 weights3 pre3 weights4 : FullWeights}
    {target : Nat}
    (cell0 : StructuredCellAt kind pre0 target 5)
    (bound0 : target < pre0.components.val.length)
    (alpha0 alpha1 alpha2 alpha3 : RawQM31)
    (halpha0 : CanonicalQM31 alpha0)
    (halpha1 : CanonicalQM31 alpha1)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (fold0 : aspis_core.sumcheck.WeightAccumulator.fold pre0 alpha0 =
      ok weights1)
    (suffix1 : List FullComponent)
    (shape1 : pre1.components.val = weights1.components.val ++ suffix1)
    (bound1 : target < weights1.components.val.length)
    (fold1 : aspis_core.sumcheck.WeightAccumulator.fold pre1 alpha1 =
      ok weights2)
    (suffix2 : List FullComponent)
    (shape2 : pre2.components.val = weights2.components.val ++ suffix2)
    (bound2 : target < weights2.components.val.length)
    (fold2 : aspis_core.sumcheck.WeightAccumulator.fold pre2 alpha2 =
      ok weights3)
    (suffix3 : List FullComponent)
    (shape3 : pre3.components.val = weights3.components.val ++ suffix3)
    (bound3 : target < weights3.components.val.length)
    (fold3 : aspis_core.sumcheck.WeightAccumulator.fold pre3 alpha3 =
      ok weights4) :
    ∃ cell4 : StructuredCellAt kind weights4 target 1,
      foldFourMeaning (toMaintainedExact alpha0) (toMaintainedExact alpha1)
          (toMaintainedExact alpha2) (toMaintainedExact alpha3)
          cell0.meaning = cell4.meaning := by
  obtain ⟨cell1, exact0⟩ := cell0.fold bound0 alpha0 halpha0 (by decide) fold0
  let cell1' :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.append cell1
      bound1 suffix1 shape1
  have pre1Bound : target < pre1.components.val.length := by
    rw [shape1]
    simp only [List.length_append]
    omega
  obtain ⟨cell2, exact1⟩ := cell1'.fold pre1Bound alpha1 halpha1
    (by decide) fold1
  let cell2' :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.append cell2
      bound2 suffix2 shape2
  have pre2Bound : target < pre2.components.val.length := by
    rw [shape2]
    simp only [List.length_append]
    omega
  obtain ⟨cell3, exact2⟩ := cell2'.fold pre2Bound alpha2 halpha2
    (by decide) fold2
  let cell3' :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.append cell3
      bound3 suffix3 shape3
  have pre3Bound : target < pre3.components.val.length := by
    rw [shape3]
    simp only [List.length_append]
    omega
  obtain ⟨cell4, exact3⟩ := cell3'.fold pre3Bound alpha3 halpha3
    (by decide) fold3
  refine ⟨cell4, ?_⟩
  have e0 : dualWeightFoldLayer 256 (toMaintainedExact alpha0)
      cell0.meaning = cell1.meaning := by
    simpa [radix4Size] using exact0
  have e1 : dualWeightFoldLayer 64 (toMaintainedExact alpha1)
      cell1'.meaning = cell2.meaning := by
    simpa [radix4Size] using exact1
  have e2 : dualWeightFoldLayer 16 (toMaintainedExact alpha2)
      cell2'.meaning = cell3.meaning := by
    simpa [radix4Size] using exact2
  have e3 : dualWeightFoldLayer 4 (toMaintainedExact alpha3)
      cell3'.meaning = cell4.meaning := by
    simpa [radix4Size] using exact3
  unfold foldFourMeaning
  rw [e0]
  change dualWeightFoldLayer 4 (toMaintainedExact alpha3)
    (dualWeightFoldLayer 16 (toMaintainedExact alpha2)
      (dualWeightFoldLayer 64 (toMaintainedExact alpha1) cell1'.meaning)) = _
  rw [e1]
  change dualWeightFoldLayer 4 (toMaintainedExact alpha3)
    (dualWeightFoldLayer 16 (toMaintainedExact alpha2) cell2'.meaning) = _
  rw [e2]
  change dualWeightFoldLayer 4 (toMaintainedExact alpha3) cell3'.meaning = _
  exact e3

/-- A tensor appended in round one follows the remaining three folds. -/
theorem StructuredCellAt.foldThree
    {kind : StructuredWeightKind}
    {pre1 weights2 pre2 weights3 pre3 weights4 : FullWeights}
    {target : Nat}
    (cell1 : StructuredCellAt kind pre1 target 4)
    (bound1 : target < pre1.components.val.length)
    (alpha1 alpha2 alpha3 : RawQM31)
    (halpha1 : CanonicalQM31 alpha1)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (fold1 : aspis_core.sumcheck.WeightAccumulator.fold pre1 alpha1 =
      ok weights2)
    (suffix2 : List FullComponent)
    (shape2 : pre2.components.val = weights2.components.val ++ suffix2)
    (bound2 : target < weights2.components.val.length)
    (fold2 : aspis_core.sumcheck.WeightAccumulator.fold pre2 alpha2 =
      ok weights3)
    (suffix3 : List FullComponent)
    (shape3 : pre3.components.val = weights3.components.val ++ suffix3)
    (bound3 : target < weights3.components.val.length)
    (fold3 : aspis_core.sumcheck.WeightAccumulator.fold pre3 alpha3 =
      ok weights4) :
    ∃ cell4 : StructuredCellAt kind weights4 target 1,
      foldThreeMeaning (toMaintainedExact alpha1) (toMaintainedExact alpha2)
          (toMaintainedExact alpha3) cell1.meaning = cell4.meaning := by
  obtain ⟨cell2, exact1⟩ := cell1.fold bound1 alpha1 halpha1 (by decide) fold1
  let cell2' :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.append cell2
      bound2 suffix2 shape2
  have pre2Bound : target < pre2.components.val.length := by
    rw [shape2]
    simp only [List.length_append]
    omega
  obtain ⟨cell3, exact2⟩ := cell2'.fold pre2Bound alpha2 halpha2
    (by decide) fold2
  let cell3' :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.append cell3
      bound3 suffix3 shape3
  have pre3Bound : target < pre3.components.val.length := by
    rw [shape3]
    simp only [List.length_append]
    omega
  obtain ⟨cell4, exact3⟩ := cell3'.fold pre3Bound alpha3 halpha3
    (by decide) fold3
  refine ⟨cell4, ?_⟩
  have e1 : dualWeightFoldLayer 64 (toMaintainedExact alpha1)
      cell1.meaning = cell2.meaning := by
    simpa [radix4Size] using exact1
  have e2 : dualWeightFoldLayer 16 (toMaintainedExact alpha2)
      cell2'.meaning = cell3.meaning := by
    simpa [radix4Size] using exact2
  have e3 : dualWeightFoldLayer 4 (toMaintainedExact alpha3)
      cell3'.meaning = cell4.meaning := by
    simpa [radix4Size] using exact3
  unfold foldThreeMeaning
  rw [e1]
  change dualWeightFoldLayer 4 (toMaintainedExact alpha3)
    (dualWeightFoldLayer 16 (toMaintainedExact alpha2) cell2'.meaning) = _
  rw [e2]
  change dualWeightFoldLayer 4 (toMaintainedExact alpha3) cell3'.meaning = _
  exact e3

/-- A tensor appended in round two follows the remaining two folds. -/
theorem StructuredCellAt.foldTwo
    {kind : StructuredWeightKind}
    {pre2 weights3 pre3 weights4 : FullWeights}
    {target : Nat}
    (cell2 : StructuredCellAt kind pre2 target 3)
    (bound2 : target < pre2.components.val.length)
    (alpha2 alpha3 : RawQM31)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (fold2 : aspis_core.sumcheck.WeightAccumulator.fold pre2 alpha2 =
      ok weights3)
    (suffix3 : List FullComponent)
    (shape3 : pre3.components.val = weights3.components.val ++ suffix3)
    (bound3 : target < weights3.components.val.length)
    (fold3 : aspis_core.sumcheck.WeightAccumulator.fold pre3 alpha3 =
      ok weights4) :
    ∃ cell4 : StructuredCellAt kind weights4 target 1,
      foldTwoMeaning (toMaintainedExact alpha2) (toMaintainedExact alpha3)
          cell2.meaning = cell4.meaning := by
  obtain ⟨cell3, exact2⟩ := cell2.fold bound2 alpha2 halpha2 (by decide) fold2
  let cell3' :=
    AspisV5AcceptedStructuredWeightJourneys.StructuredCellAt.append cell3
      bound3 suffix3 shape3
  have pre3Bound : target < pre3.components.val.length := by
    rw [shape3]
    simp only [List.length_append]
    omega
  obtain ⟨cell4, exact3⟩ := cell3'.fold pre3Bound alpha3 halpha3
    (by decide) fold3
  refine ⟨cell4, ?_⟩
  have e2 : dualWeightFoldLayer 16 (toMaintainedExact alpha2)
      cell2.meaning = cell3.meaning := by
    simpa [radix4Size] using exact2
  have e3 : dualWeightFoldLayer 4 (toMaintainedExact alpha3)
      cell3'.meaning = cell4.meaning := by
    simpa [radix4Size] using exact3
  unfold foldTwoMeaning
  rw [e2]
  change dualWeightFoldLayer 4 (toMaintainedExact alpha3) cell3'.meaning = _
  exact e3

/-- A tensor appended in round three follows the final fold. -/
theorem StructuredCellAt.foldOne
    {kind : StructuredWeightKind} {pre3 weights4 : FullWeights}
    {target : Nat}
    (cell3 : StructuredCellAt kind pre3 target 2)
    (bound3 : target < pre3.components.val.length)
    (alpha3 : RawQM31) (halpha3 : CanonicalQM31 alpha3)
    (fold3 : aspis_core.sumcheck.WeightAccumulator.fold pre3 alpha3 =
      ok weights4) :
    ∃ cell4 : StructuredCellAt kind weights4 target 1,
      foldOneMeaning (toMaintainedExact alpha3) cell3.meaning =
        cell4.meaning := by
  obtain ⟨cell4, exact3⟩ := cell3.fold bound3 alpha3 halpha3
    (by decide) fold3
  refine ⟨cell4, ?_⟩
  simpa [foldOneMeaning, radix4Size] using exact3

#print axioms StructuredCellAt.append
#print axioms StructuredCellAt.foldFour
#print axioms StructuredCellAt.foldThree
#print axioms StructuredCellAt.foldTwo
#print axioms StructuredCellAt.foldOne

end AspisV5AcceptedStructuredWeightJourneys
