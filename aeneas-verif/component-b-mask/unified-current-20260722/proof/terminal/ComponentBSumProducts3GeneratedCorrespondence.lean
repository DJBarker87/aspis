import ComponentBOptimizedPrimitiveBridge
import SumProductsFullCorrespondence

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBRealEvaluatorProof

private theorem canonicalArrayToRetarget
    (values : Array QM31 3#usize) (canonical : CanonicalArray values) :
    AspisLane5QM31SumProductsProof.CanonicalQM31Array values := by
  intro index hindex
  have h := canonical ⟨index, hindex⟩
  have hbound : index < values.val.length := by
    simpa [Array.length_eq] using hindex
  have helem : values.val[index]! = values.val[index] := by
    apply List.getElem!_of_getElem?
    simp
  rw [helem]
  exact h

private theorem listGetBangEq
    {T : Type} [Inhabited T] (values : List T) (index : Nat)
    (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem generatedToExactEqRetarget (value : QM31) :
    generatedQm31ToExact value =
      AspisLane5QM31SumProductsProof.qm31ToExact value := by
  rfl

private theorem retargetExactProductDotEqFinSum
    (left right : Array QM31 3#usize) :
    AspisLane5QM31SumProductsProof.exactProductDot left right =
      ∑ i : Fin 3,
        generatedQm31ToExact left.val[i.val] *
    generatedQm31ToExact right.val[i.val] := by
  have left0 := listGetBangEq left.val 0 (by simpa [Array.length_eq])
  have left1 := listGetBangEq left.val 1 (by simpa [Array.length_eq])
  have left2 := listGetBangEq left.val 2 (by simpa [Array.length_eq])
  have right0 := listGetBangEq right.val 0 (by simpa [Array.length_eq])
  have right1 := listGetBangEq right.val 1 (by simpa [Array.length_eq])
  have right2 := listGetBangEq right.val 2 (by simpa [Array.length_eq])
  change
    (∑ index ∈ Finset.range (3#usize).val,
      AspisLane5QM31SumProductsProof.qm31ToExact left.val[index]! *
        AspisLane5QM31SumProductsProof.qm31ToExact right.val[index]!) = _
  norm_num only [UScalar.ofNatCore_val_eq]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  simp [
    AspisLane5QM31SumProductsProof.qm31ToExact,
    AspisLane5QM31SumProductsProof.cm31ToExact,
    AspisLane5QM31SumProductsProof.qm31R,
    generatedQm31ToExact, generatedCm31ToExact, exactQm31R,
    Fin.sum_univ_succ, left0, left1, left2, right0, right1, right2]
  exact add_assoc _ _ _

/-- The fresh combined owning-crate extraction's actual `qm31_sum_products3`
body has the exact three-product semantics required by the generated evaluator.
The proof replays the authenticated channel, component, outer-loop, no-wrap,
and reconstruction theorems against that combined module. -/
theorem generated_sumProducts3_correspondence_current_field :
    GeneratedSumProducts3Correspondence := by
  intro left right hleft hright
  obtain ⟨out, hrun, hcanonical, hexact⟩ :=
    AspisLane5QM31SumProductsProof.extracted_qm31_sum_products3_corresponds
      left right (canonicalArrayToRetarget left hleft)
        (canonicalArrayToRetarget right hright)
  refine ⟨out, hrun, hcanonical, ?_⟩
  rw [generatedToExactEqRetarget out, hexact]
  exact retargetExactProductDotEqFinSum left right

/-- On the recorded 64-bit extraction target, all three optimized primitive
fields required by the fresh generated evaluator are discharged. -/
theorem optimizedPrimitiveCorrespondence_current_field
    :
    OptimizedPrimitiveCorrespondence :=
  optimizedPrimitiveCorrespondence_of_sumProducts3
    generated_sumProducts3_correspondence_current_field

#print axioms generated_sumProducts3_correspondence_current_field
#print axioms optimizedPrimitiveCorrespondence_current_field

end ComponentBRealEvaluatorProof
