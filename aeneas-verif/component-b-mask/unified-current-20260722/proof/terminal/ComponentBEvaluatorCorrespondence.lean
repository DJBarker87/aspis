import ComponentBEvaluatorOperationalProof
import ComponentBEvaluatorProof

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBRealEvaluatorProof

private theorem canonicalAt'
    (polynomial : Polynomial) (canonical : CanonicalArray polynomial)
    (i : Nat) (hi : i < 28) :
    GeneratedCanonicalQM31 (coefficientAt polynomial ⟨i, hi⟩) :=
  canonical ⟨i, hi⟩

private theorem blockCoefficientsCanonical'
    (polynomial : Polynomial) (canonical : CanonicalArray polynomial)
    (block : Nat) (hblock : block < 7) :
    CanonicalArray (Array.make 3#usize [
      coefficientAt polynomial ⟨4 * block + 1, by omega⟩,
      coefficientAt polynomial ⟨4 * block + 2, by omega⟩,
      coefficientAt polynomial ⟨4 * block + 3, by omega⟩]) := by
  intro i
  fin_cases i <;>
    simpa [Array.make] using
      canonicalAt' polynomial canonical _ (by omega)

private theorem powersCanonical'
    (x x2 x3 : QM31)
    (hx : GeneratedCanonicalQM31 x)
    (hx2 : GeneratedCanonicalQM31 x2)
    (hx3 : GeneratedCanonicalQM31 x3) :
    CanonicalArray (Array.make 3#usize [x, x2, x3]) := by
  intro i
  fin_cases i
  · simpa [Array.make] using hx
  · simpa [Array.make] using hx2
  · simpa [Array.make] using hx3

/-- The actual extracted public Rust evaluator returns the exact degree-27
polynomial value.  The single premise contains only exact semantics of the
three optimized field primitives not yet covered by the authenticated field
bundle; it contains no evaluator or recurrence assertion. -/
theorem generated_evaluator_exact_of_optimized_primitives
    (primitives : OptimizedPrimitiveCorrespondence)
    (polynomial : Polynomial) (challenge : QM31)
    (canonicalPolynomial : CanonicalArray polynomial)
    (canonicalChallenge : GeneratedCanonicalQM31 challenge) :
    ∃ out,
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
          polynomial challenge = .ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        exactDegree27Evaluation polynomial (generatedQm31ToExact challenge) := by
  obtain ⟨x2, hx2Run, hx2Canonical, hx2Exact⟩ :=
    primitives.square challenge canonicalChallenge
  obtain ⟨x3, hx3Run, hx3Canonical, hx3Exact⟩ :=
    generated_qm31_mul_corresponds challenge x2 canonicalChallenge hx2Canonical
  obtain ⟨x4, hx4Run, hx4Canonical, hx4Exact⟩ :=
    primitives.square x2 hx2Canonical
  obtain ⟨prepared, preparedRun, preparedMul⟩ :=
    primitives.prepared x4 hx4Canonical
  let powers : Array QM31 3#usize := Array.make 3#usize [challenge, x2, x3]
  have powersCanonical : CanonicalArray powers :=
    powersCanonical' challenge x2 x3 canonicalChallenge hx2Canonical hx3Canonical

  have blockResult : ∀ (block : Nat) (hblock : block < 7), ∃ out,
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call
        ((polynomial, powers) :
          ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure)
        (blockScalar block hblock) = .ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        exactBlock polynomial (generatedQm31ToExact challenge) ⟨block, hblock⟩ := by
    intro block hblock
    obtain ⟨products, productsRun, productsCanonical, productsExact⟩ :=
      primitives.sumProducts3 powers
        (Array.make 3#usize [
          coefficientAt polynomial ⟨4 * block + 1, by omega⟩,
          coefficientAt polynomial ⟨4 * block + 2, by omega⟩,
          coefficientAt polynomial ⟨4 * block + 3, by omega⟩])
        powersCanonical
        (blockCoefficientsCanonical' polynomial canonicalPolynomial block hblock)
    obtain ⟨out, addRun, outCanonical, outExact⟩ :=
      generated_qm31_add_corresponds
        (coefficientAt polynomial ⟨4 * block, by omega⟩) products
        (canonicalAt' polynomial canonicalPolynomial _ (by omega))
        productsCanonical
    refine ⟨out,
      generated_block_call_runs polynomial powers block hblock
        products out productsRun addRun,
      outCanonical, ?_⟩
    rw [outExact, productsExact]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    simp [exactBlock, powers, Array.make, coefficientAt, hx2Exact, hx3Exact]
    ring

  obtain ⟨b6, b6Run, b6Canonical, b6Exact⟩ := blockResult 6 (by omega)
  obtain ⟨b5, b5Run, b5Canonical, b5Exact⟩ := blockResult 5 (by omega)
  obtain ⟨b4, b4Run, b4Canonical, b4Exact⟩ := blockResult 4 (by omega)
  obtain ⟨b3, b3Run, b3Canonical, b3Exact⟩ := blockResult 3 (by omega)
  obtain ⟨b2, b2Run, b2Canonical, b2Exact⟩ := blockResult 2 (by omega)
  obtain ⟨b1, b1Run, b1Canonical, b1Exact⟩ := blockResult 1 (by omega)
  obtain ⟨b0, b0Run, b0Canonical, b0Exact⟩ := blockResult 0 (by omega)

  obtain ⟨m5, m5Run, m5Canonical, m5Exact⟩ := preparedMul b6 b6Canonical
  obtain ⟨a5, a5Run, a5Canonical, a5Exact⟩ :=
    generated_qm31_add_corresponds m5 b5 m5Canonical b5Canonical
  obtain ⟨m4, m4Run, m4Canonical, m4Exact⟩ := preparedMul a5 a5Canonical
  obtain ⟨a4, a4Run, a4Canonical, a4Exact⟩ :=
    generated_qm31_add_corresponds m4 b4 m4Canonical b4Canonical
  obtain ⟨m3, m3Run, m3Canonical, m3Exact⟩ := preparedMul a4 a4Canonical
  obtain ⟨a3, a3Run, a3Canonical, a3Exact⟩ :=
    generated_qm31_add_corresponds m3 b3 m3Canonical b3Canonical
  obtain ⟨m2, m2Run, m2Canonical, m2Exact⟩ := preparedMul a3 a3Canonical
  obtain ⟨a2, a2Run, a2Canonical, a2Exact⟩ :=
    generated_qm31_add_corresponds m2 b2 m2Canonical b2Canonical
  obtain ⟨m1, m1Run, m1Canonical, m1Exact⟩ := preparedMul a2 a2Canonical
  obtain ⟨a1, a1Run, a1Canonical, a1Exact⟩ :=
    generated_qm31_add_corresponds m1 b1 m1Canonical b1Canonical
  obtain ⟨m0, m0Run, m0Canonical, m0Exact⟩ := preparedMul a1 a1Canonical
  obtain ⟨a0, a0Run, a0Canonical, a0Exact⟩ :=
    generated_qm31_add_corresponds m0 b0 m0Canonical b0Canonical

  have loopRun := generated_evaluator_loop_runs powers prepared polynomial
    b6 b5 b4 b3 b2 b1 b0 m5 a5 m4 a4 m3 a3 m2 a2 m1 a1 m0 a0
    b5Run b4Run b3Run b2Run b1Run b0Run
    m5Run a5Run m4Run a4Run m3Run a3Run m2Run a2Run m1Run a1Run m0Run a0Run
  have scalarSix : blockScalar 6 (by omega) = 6#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  refine ⟨a0, ?_, a0Canonical, ?_⟩
  · unfold ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
    simp [hx2Run, hx3Run, hx4Run, preparedRun]
    change (do
      let accumulator ←
        ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeQM31.call
          ((polynomial, powers) :
            ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial.closure)
          6#usize
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial_loop
        powers prepared polynomial accumulator 6#usize) = .ok a0
    rw [← scalarSix, b6Run]
    exact loopRun
  · rw [a0Exact, m0Exact, a1Exact, m1Exact, a2Exact, m2Exact,
      a3Exact, m3Exact, a4Exact, m4Exact, a5Exact, m5Exact,
      b0Exact, b1Exact, b2Exact, b3Exact, b4Exact, b5Exact, b6Exact,
      hx4Exact, hx2Exact]
    rw [← exactRadixFour_eq_degree27]
    simp [exactRadixFour]
    ring

#print axioms generated_evaluator_exact_of_optimized_primitives

end ComponentBRealEvaluatorProof
