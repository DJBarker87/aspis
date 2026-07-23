import ComponentBEvaluatorCorrespondence

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBPublicEvaluateProof

abbrev QM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev Polynomial := Array QM31 28#usize
abbrev Mask := ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask

private abbrev roundPolynomial :=
  ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial

private abbrev evaluatePolynomial :=
  ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial

/-- The extracted public Rust wrapper executes exactly ten generated
round-polynomial/evaluator steps, in the order 0 through 9.  The round-count
bound is the extracted Rust constant, whose generated body is `10`; it is not
an assumed transcript parameter. -/
theorem generated_public_evaluate_ten_round_recurrence
    (mask : Mask) (point : Array QM31 10#usize)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Polynomial)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : QM31)
    (hr0 : roundPolynomial mask 0#usize mask.initial_claim = .ok (.some p0))
    (he0 : evaluatePolynomial p0 point.val[0] = .ok c1)
    (hr1 : roundPolynomial mask 1#usize c1 = .ok (.some p1))
    (he1 : evaluatePolynomial p1 point.val[1] = .ok c2)
    (hr2 : roundPolynomial mask 2#usize c2 = .ok (.some p2))
    (he2 : evaluatePolynomial p2 point.val[2] = .ok c3)
    (hr3 : roundPolynomial mask 3#usize c3 = .ok (.some p3))
    (he3 : evaluatePolynomial p3 point.val[3] = .ok c4)
    (hr4 : roundPolynomial mask 4#usize c4 = .ok (.some p4))
    (he4 : evaluatePolynomial p4 point.val[4] = .ok c5)
    (hr5 : roundPolynomial mask 5#usize c5 = .ok (.some p5))
    (he5 : evaluatePolynomial p5 point.val[5] = .ok c6)
    (hr6 : roundPolynomial mask 6#usize c6 = .ok (.some p6))
    (he6 : evaluatePolynomial p6 point.val[6] = .ok c7)
    (hr7 : roundPolynomial mask 7#usize c7 = .ok (.some p7))
    (he7 : evaluatePolynomial p7 point.val[7] = .ok c8)
    (hr8 : roundPolynomial mask 8#usize c8 = .ok (.some p8))
    (he8 : evaluatePolynomial p8 point.val[8] = .ok c9)
    (hr9 : roundPolynomial mask 9#usize c9 = .ok (.some p9))
    (he9 : evaluatePolynomial p9 point.val[9] = .ok c10) :
    ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate mask point =
      .ok c10 := by
  rcases System.Platform.numBits_eq with targetWidth | targetWidth
  all_goals
  have add01 : Usize.wrapping_add 0#usize 1#usize = 1#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  have add12 : Usize.wrapping_add 1#usize 1#usize = 2#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  have add23 : Usize.wrapping_add 2#usize 1#usize = 3#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  have add34 : Usize.wrapping_add 3#usize 1#usize = 4#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  have add45 : Usize.wrapping_add 4#usize 1#usize = 5#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  have add56 : Usize.wrapping_add 5#usize 1#usize = 6#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  have add67 : Usize.wrapping_add 6#usize 1#usize = 7#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  have add78 : Usize.wrapping_add 7#usize 1#usize = 8#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  have add89 : Usize.wrapping_add 8#usize 1#usize = 9#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  have add910 : Usize.wrapping_add 9#usize 1#usize = 10#usize := by
    apply UScalar.eq_of_val_eq
    simp [Usize.size, Usize.numBits, targetWidth]
  rcases mask with ⟨initial, rounds⟩
  unfold ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate
  unfold ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr0, he0, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr1, he1, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr2, he2, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr3, he3, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr4, he4, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr5, he5, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr6, he6, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr7, he7, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr8, he8, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS,
    hr9, he9, Array.index_usize, Aeneas.Std.lift, UScalar.wrapping_add, Usize.size, Usize.numBits, targetWidth]
  rw [Aeneas.Std.loop.eq_def]
  simp_all [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate_loop.body,
    ComponentBGenerated.aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS]

#print axioms generated_public_evaluate_ten_round_recurrence

private theorem evaluator_run_is_exact
    (primitives : ComponentBRealEvaluatorProof.OptimizedPrimitiveCorrespondence)
    (polynomial : Polynomial) (challenge out : QM31)
    (canonicalPolynomial : ComponentBRealEvaluatorProof.CanonicalArray polynomial)
    (canonicalChallenge : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 challenge)
    (run : evaluatePolynomial polynomial challenge = .ok out) :
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation polynomial
          (ComponentBRealEvaluatorProof.generatedQm31ToExact challenge) := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    ComponentBRealEvaluatorProof.generated_evaluator_exact_of_optimized_primitives
      primitives polynomial challenge canonicalPolynomial canonicalChallenge
  have hout : out = candidate := Result.ok.inj (run.symm.trans candidateRun)
  subst out
  exact ⟨candidateCanonical, candidateExact⟩

/-- The actual extracted public wrapper, the actual extracted round helper,
and the actual extracted degree-27 evaluator form one exact ten-round terminal
recurrence.  No claim about Fiat--Shamir binding or PCS authentication is part
of this local arithmetic theorem. -/
theorem generated_public_evaluate_exact_ten_round_terminal
    (primitives : ComponentBRealEvaluatorProof.OptimizedPrimitiveCorrespondence)
    (mask : Mask) (point : Array QM31 10#usize)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Polynomial)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : QM31)
    (pointCanonical : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 point.val[i.val])
    (cp0 : ComponentBRealEvaluatorProof.CanonicalArray p0)
    (cp1 : ComponentBRealEvaluatorProof.CanonicalArray p1)
    (cp2 : ComponentBRealEvaluatorProof.CanonicalArray p2)
    (cp3 : ComponentBRealEvaluatorProof.CanonicalArray p3)
    (cp4 : ComponentBRealEvaluatorProof.CanonicalArray p4)
    (cp5 : ComponentBRealEvaluatorProof.CanonicalArray p5)
    (cp6 : ComponentBRealEvaluatorProof.CanonicalArray p6)
    (cp7 : ComponentBRealEvaluatorProof.CanonicalArray p7)
    (cp8 : ComponentBRealEvaluatorProof.CanonicalArray p8)
    (cp9 : ComponentBRealEvaluatorProof.CanonicalArray p9)
    (hr0 : roundPolynomial mask 0#usize mask.initial_claim = .ok (.some p0))
    (he0 : evaluatePolynomial p0 point.val[0] = .ok c1)
    (hr1 : roundPolynomial mask 1#usize c1 = .ok (.some p1))
    (he1 : evaluatePolynomial p1 point.val[1] = .ok c2)
    (hr2 : roundPolynomial mask 2#usize c2 = .ok (.some p2))
    (he2 : evaluatePolynomial p2 point.val[2] = .ok c3)
    (hr3 : roundPolynomial mask 3#usize c3 = .ok (.some p3))
    (he3 : evaluatePolynomial p3 point.val[3] = .ok c4)
    (hr4 : roundPolynomial mask 4#usize c4 = .ok (.some p4))
    (he4 : evaluatePolynomial p4 point.val[4] = .ok c5)
    (hr5 : roundPolynomial mask 5#usize c5 = .ok (.some p5))
    (he5 : evaluatePolynomial p5 point.val[5] = .ok c6)
    (hr6 : roundPolynomial mask 6#usize c6 = .ok (.some p6))
    (he6 : evaluatePolynomial p6 point.val[6] = .ok c7)
    (hr7 : roundPolynomial mask 7#usize c7 = .ok (.some p7))
    (he7 : evaluatePolynomial p7 point.val[7] = .ok c8)
    (hr8 : roundPolynomial mask 8#usize c8 = .ok (.some p8))
    (he8 : evaluatePolynomial p8 point.val[8] = .ok c9)
    (hr9 : roundPolynomial mask 9#usize c9 = .ok (.some p9))
    (he9 : evaluatePolynomial p9 point.val[9] = .ok c10) :
    ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate mask point = .ok c10 ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c1 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p0
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[0]) ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c2 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p1
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[1]) ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c3 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p2
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[2]) ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c4 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p3
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[3]) ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c5 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p4
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[4]) ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c6 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p5
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[5]) ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c7 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p6
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[6]) ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c8 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p7
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[7]) ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c9 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p8
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[8]) ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact c10 =
        ComponentBRealEvaluatorProof.exactDegree27Evaluation p9
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[9]) := by
  have e0 := evaluator_run_is_exact primitives p0 point.val[0] c1 cp0
    (pointCanonical ⟨0, by omega⟩) he0
  have e1 := evaluator_run_is_exact primitives p1 point.val[1] c2 cp1
    (pointCanonical ⟨1, by omega⟩) he1
  have e2 := evaluator_run_is_exact primitives p2 point.val[2] c3 cp2
    (pointCanonical ⟨2, by omega⟩) he2
  have e3 := evaluator_run_is_exact primitives p3 point.val[3] c4 cp3
    (pointCanonical ⟨3, by omega⟩) he3
  have e4 := evaluator_run_is_exact primitives p4 point.val[4] c5 cp4
    (pointCanonical ⟨4, by omega⟩) he4
  have e5 := evaluator_run_is_exact primitives p5 point.val[5] c6 cp5
    (pointCanonical ⟨5, by omega⟩) he5
  have e6 := evaluator_run_is_exact primitives p6 point.val[6] c7 cp6
    (pointCanonical ⟨6, by omega⟩) he6
  have e7 := evaluator_run_is_exact primitives p7 point.val[7] c8 cp7
    (pointCanonical ⟨7, by omega⟩) he7
  have e8 := evaluator_run_is_exact primitives p8 point.val[8] c9 cp8
    (pointCanonical ⟨8, by omega⟩) he8
  have e9 := evaluator_run_is_exact primitives p9 point.val[9] c10 cp9
    (pointCanonical ⟨9, by omega⟩) he9
  refine ⟨generated_public_evaluate_ten_round_recurrence mask point
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
      hr0 he0 hr1 he1 hr2 he2 hr3 he3 hr4 he4 hr5 he5 hr6 he6 hr7 he7
      hr8 he8 hr9 he9,
    e0.2, e1.2, e2.2, e3.2, e4.2, e5.2, e6.2, e7.2, e8.2, e9.2⟩

#print axioms generated_public_evaluate_exact_ten_round_terminal

end ComponentBPublicEvaluateProof
