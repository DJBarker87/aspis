import ComponentBMixedEndpointProof
import ComponentBMaintainedTerminalBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBUnifiedTransportFree

abbrev QM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev ExactQM31 := ComponentBGenerated.MultilinearEvalProofs.ExactQM31
abbrev Polynomial := Array QM31 28#usize

private def rawCoefficient (polynomial : Polynomial) (coefficient : Fin 28) :
    QM31 :=
  polynomial.val[coefficient.val]'(by
    simpa [polynomial.property] using coefficient.isLt)

private def rawTailCoefficient (polynomial : Polynomial)
    (coefficient : Fin 27) : QM31 :=
  rawCoefficient polynomial ⟨coefficient.val + 1, by omega⟩

private theorem mapSumHeadTail
    (polynomial : Polynomial) (f : QM31 → ExactQM31) :
    (polynomial.val.map f).sum =
      f polynomial.val[0] + (polynomial.val.tail.map f).sum := by
  have hnonempty : polynomial.val ≠ [] := by
    intro hempty
    have hlength := polynomial.property
    rw [hempty] at hlength
    simp at hlength
  calc
    (polynomial.val.map f).sum =
        ((polynomial.val.head hnonempty :: polynomial.val.tail).map f).sum := by
      rw [List.cons_head_tail hnonempty]
    _ = f polynomial.val[0] + (polynomial.val.tail.map f).sum := by
      rw [List.head_eq_getElem hnonempty]
      rfl

private theorem tailMapEqOfFn (polynomial : Polynomial) :
    polynomial.val.tail.map
        ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact =
      List.ofFn (fun coefficient : Fin 27 ↦
        ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact
          (rawTailCoefficient polynomial coefficient)) := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_tail, polynomial.property,
      List.length_ofFn]
    norm_num
  · intro index leftBound rightBound
    rw [List.getElem_map, List.getElem_tail, List.getElem_ofFn]
    simp [rawTailCoefficient, rawCoefficient]

private theorem exactBoundary_eq_maintained (polynomial : Polynomial) :
    ComponentBGenerated.v5_sumcheck_mask.exactBoundary polynomial =
      2 * ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact
          (rawCoefficient polynomial ⟨0, by omega⟩) +
        ∑ coefficient : Fin 27,
          ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact
            (rawTailCoefficient polynomial coefficient) := by
  rw [ComponentBGenerated.v5_sumcheck_mask.exactBoundary]
  rw [mapSumHeadTail polynomial]
  rw [tailMapEqOfFn]
  rw [List.sum_ofFn]
  let a := ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact
    polynomial.val[0]
  let tailSum := ∑ coefficient : Fin 27,
    ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact
      (rawTailCoefficient polynomial coefficient)
  change a + (a + tailSum) = 2 * a + tailSum
  rw [two_mul]
  exact (add_assoc a a tailSum).symm

private theorem generatedZeroExact :
    ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact
        ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero = 0 := by
  rfl

/-- An actual successful generated zero-boundary call entails the maintained
exact zero-boundary invariant for exactly the same generated polynomial. -/
theorem generated_zero_boundary_implies_exact
    (polynomial : Polynomial)
    (hzero :
      ComponentBGenerated.aspis_core.state_only_sumcheck.state_only_boundary_sum
          polynomial =
        .ok ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero) :
    ComponentBMaintainedTerminalBridge.ExactZeroBoundary polynomial := by
  obtain ⟨output, hcall, _hcanonical, hexact⟩ :=
    ComponentBGenerated.v5_sumcheck_mask.generatedBoundaryCorresponds polynomial
  have outputEq : output =
      ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero :=
    Result.ok.inj (hcall.symm.trans hzero)
  subst output
  unfold ComponentBMaintainedTerminalBridge.ExactZeroBoundary
  unfold ComponentBMaintainedTerminalBridge.exactConstant
    ComponentBMaintainedTerminalBridge.exactTail
    ComponentBRealEvaluatorProof.coefficientAt
  change
    2 * ComponentBRealEvaluatorProof.generatedQm31ToExact polynomial.val[0] +
        ∑ coefficient : Fin 27,
          ComponentBRealEvaluatorProof.generatedQm31ToExact
            (rawTailCoefficient polynomial coefficient) = 0
  unfold ComponentBRealEvaluatorProof.generatedQm31ToExact
    ComponentBRealEvaluatorProof.generatedCm31ToExact
    ComponentBRealEvaluatorProof.exactQm31R
  change
    2 * ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact
          (rawCoefficient polynomial ⟨0, by omega⟩) +
        ∑ coefficient : Fin 27,
          ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact
            (rawTailCoefficient polynomial coefficient) = 0
  rw [← exactBoundary_eq_maintained polynomial]
  rw [← hexact]
  exact generatedZeroExact

/-- Conversely, canonical coefficients satisfying the maintained exact
zero-boundary equation make the authentic generated boundary wrapper return
the generated zero value. -/
theorem exact_zero_boundary_implies_generated
    (polynomial : Polynomial)
    (canonical : ∀ coefficient : Fin 28,
      ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalQM31
        polynomial.val[coefficient.val])
    (hzero : ComponentBMaintainedTerminalBridge.ExactZeroBoundary polynomial) :
    ComponentBGenerated.aspis_core.state_only_sumcheck.state_only_boundary_sum
        polynomial =
      .ok ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero := by
  obtain ⟨output, hcall, outputCanonical, outputExact⟩ :=
    ComponentBGenerated.v5_sumcheck_mask.generatedBoundaryCorresponds polynomial
  have exactBoundaryZero :
      ComponentBGenerated.v5_sumcheck_mask.exactBoundary polynomial = 0 := by
    rw [exactBoundary_eq_maintained]
    unfold ComponentBMaintainedTerminalBridge.ExactZeroBoundary at hzero
    unfold ComponentBMaintainedTerminalBridge.exactConstant
      ComponentBMaintainedTerminalBridge.exactTail
      ComponentBRealEvaluatorProof.coefficientAt at hzero
    change
      2 * ComponentBRealEvaluatorProof.generatedQm31ToExact polynomial.val[0] +
          ∑ coefficient : Fin 27,
            ComponentBRealEvaluatorProof.generatedQm31ToExact
              (rawTailCoefficient polynomial coefficient) = 0 at hzero
    unfold ComponentBRealEvaluatorProof.generatedQm31ToExact
      ComponentBRealEvaluatorProof.generatedCm31ToExact
      ComponentBRealEvaluatorProof.exactQm31R at hzero
    exact hzero
  have zeroCanonical :
      ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalQM31
        ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero := by
    norm_num [ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero,
      ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalQM31,
      ComponentBGenerated.MultilinearEvalProofs.GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus]
  have outputExactZero :
      ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact output =
        ComponentBGenerated.MultilinearEvalProofs.generatedQm31ToExact
          ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero := by
    rw [outputExact, exactBoundaryZero]
    exact generatedZeroExact.symm
  have outputEq :=
    ComponentBGenerated.v5_sumcheck_mask.generatedQm31ToExactInjective
      output ComponentBGenerated.v5_sumcheck_mask.extractedQM31Zero
      outputCanonical zeroCanonical outputExactZero
  simpa [outputEq] using hcall

#print axioms generated_zero_boundary_implies_exact
#print axioms exact_zero_boundary_implies_generated

end ComponentBUnifiedTransportFree
