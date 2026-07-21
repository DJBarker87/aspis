import ComponentBPublicEvaluateRecurrence
import ComponentBSumProducts3GeneratedCorrespondence

namespace ComponentBRealEvaluatorProof

/-- The current owning-crate extraction's real degree-27 evaluator has exact
polynomial semantics.  The optimized primitive premise is discharged by the
fresh extraction of the current `field.rs` implementation; only the recorded
64-bit extraction target and the evaluator's canonical-input hypotheses remain.
-/
theorem generated_evaluator_exact_current_field
    (targetWidth : System.Platform.numBits = 64)
    (polynomial : Polynomial) (challenge : QM31)
    (canonicalPolynomial : CanonicalArray polynomial)
    (canonicalChallenge : GeneratedCanonicalQM31 challenge) :
    ∃ out,
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
          polynomial challenge = .ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        exactDegree27Evaluation polynomial (generatedQm31ToExact challenge) :=
  generated_evaluator_exact_of_optimized_primitives
    (optimizedPrimitiveCorrespondence_current_field targetWidth)
    polynomial challenge canonicalPolynomial canonicalChallenge

#print axioms generated_evaluator_exact_current_field

end ComponentBRealEvaluatorProof
