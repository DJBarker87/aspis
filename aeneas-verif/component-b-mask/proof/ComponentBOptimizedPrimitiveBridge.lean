import ComponentBEvaluatorProof

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBRealEvaluatorProof

/-- The only field fact still needed by the evaluator after discharging the
specialized square and prepared-multiply bodies against the authentic combined
extraction. -/
def GeneratedSumProducts3Correspondence : Prop :=
  ∀ left right,
    CanonicalArray left → CanonicalArray right →
    ∃ out,
      ComponentBGenerated.aspis_core.field.qm31_sum_products3 left right =
          .ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        ∑ i : Fin 3,
          generatedQm31ToExact left.val[i.val] *
            generatedQm31ToExact right.val[i.val]

/-- The authentic evaluator's former three-field arithmetic premise reduces
to exactly its generated three-product kernel.  Target width, specialized
square, prepared-cache construction, and prepared multiplication are all
discharged here. -/
theorem optimizedPrimitiveCorrespondence_of_sumProducts3
    (targetWidth : System.Platform.numBits = 64)
    (sumProducts3 : GeneratedSumProducts3Correspondence) :
    OptimizedPrimitiveCorrespondence := by
  refine {
    targetWidth := targetWidth
    square := generated_qm31_square_corresponds
    prepared := generated_prepared_new_mul_corresponds
    sumProducts3 := ?_
  }
  exact sumProducts3

#print axioms optimizedPrimitiveCorrespondence_of_sumProducts3

end ComponentBRealEvaluatorProof
