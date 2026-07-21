import ComponentBSumProducts3OperationalAdapterD1E7

namespace ComponentBRealEvaluatorProof

/-- All optimized evaluator primitives for the current owning-crate extraction,
including the generated fused three-product graph.  The only argument records
the replay bundle's authenticated 64-bit extraction target. -/
theorem optimizedPrimitiveCorrespondence_operational_d1e7
    (targetWidth : System.Platform.numBits = 64) :
    OptimizedPrimitiveCorrespondence := by
  refine {
    targetWidth := targetWidth
    square := generated_qm31_square_corresponds
    prepared := generated_prepared_new_mul_corresponds
    sumProducts3 := ?_
  }
  exact
    SumProducts3OperationalAdapterD1E7.generated_sumProducts3_operational_correspondence_d1e7

#print axioms optimizedPrimitiveCorrespondence_operational_d1e7

end ComponentBRealEvaluatorProof
