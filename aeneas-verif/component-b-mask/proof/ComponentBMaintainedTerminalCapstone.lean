import ComponentBDegree27CoordinateFormulaD1E7
import ComponentBCurrentFieldEvaluatorCorrespondence

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBMaintainedTerminalBridge

noncomputable local instance : Field ExactQM31 := by
  change Field AspisV5ComponentCQM31TowerExact.QM31Exact
  infer_instance

private theorem exact_two_ne_zero : (2 : ExactQM31) ≠ 0 := by
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  have hrere := congrArg QuadraticAlgebra.re hre
  change (2 : AspisAeneasCM31Exact.M31Exact) = 0 at hrere
  exact (by decide : (2 : AspisAeneasCM31Exact.M31Exact) ≠ 0) hrere

/-- One authentic extracted round update followed by the authentic extracted
degree-27 evaluator is the maintained `maskStep`. -/
theorem generated_round_evaluation_eq_maskStep
    (primitives : ComponentBRealEvaluatorProof.OptimizedPrimitiveCorrespondence)
    (coordinateFormula : Degree27CoordinateFormula)
    (mask : Mask) (round : Fin 10)
    (incoming halfValue updated challenge out : QM31)
    (polynomial : Polynomial)
    (hincoming : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 incoming)
    (hstored : ComponentBRealEvaluatorProof.CanonicalArray (storedRound mask round))
    (hzero : ExactZeroBoundary (storedRound mask round))
    (hchallenge : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 challenge)
    (hpolynomialCanonical : ComponentBRealEvaluatorProof.CanonicalArray polynomial)
    (hhalf : ComponentBGenerated.aspis_core.field.QM31.half incoming = .ok halfValue)
    (hadd : ComponentBGenerated.aspis_core.field.QM31.add
      (storedRound mask round).val[0] halfValue = .ok updated)
    (hround : ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial
      mask (roundUsize primitives.targetWidth round) incoming =
        .ok (.some polynomial))
    (hevaluate :
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
        polynomial challenge = .ok out) :
    ComponentBRealEvaluatorProof.generatedQm31ToExact out =
      AspisV5SumcheckCommitment.maskStep
        (ComponentBRealEvaluatorProof.generatedQm31ToExact incoming)
        (exactTail (storedRound mask round))
        (ComponentBRealEvaluatorProof.generatedQm31ToExact challenge) := by
  let roundScalar : Std.Usize := roundUsize primitives.targetWidth round
  have hsome : mask.zero_boundary_rounds.val[roundScalar.val]? =
      some (storedRound mask round) := by
    change mask.zero_boundary_rounds.val[round.val]? = _
    simp [storedRound, round.isLt]
  have generatedRound :
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial
          mask roundScalar incoming =
        .ok (.some ((storedRound mask round).set 0#usize updated)) := by
    simp [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial,
      lift, Array.to_slice, core.slice.Slice.get,
      core.slice.index.Usize.get, hsome, hhalf, hadd,
      Array.index_usize, Array.update]
    apply Subtype.ext
    rfl
  have hpolynomial :
      polynomial = (storedRound mask round).set 0#usize updated := by
    exact Option.some.inj (Result.ok.inj (hround.symm.trans generatedRound))
  have halfExact := generated_half_exact incoming halfValue exact_two_ne_zero
    hincoming hhalf
  have storedZeroCanonical :
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        (storedRound mask round).val[0] :=
    hstored ⟨0, by norm_num⟩
  have updatedExact := generated_add_exact_of_run
    (storedRound mask round).val[0] halfValue updated
    storedZeroCanonical halfExact.1 hadd
  obtain ⟨candidate, candidateRun, _, candidateExact⟩ :=
    ComponentBRealEvaluatorProof.generated_evaluator_exact_of_optimized_primitives
      primitives polynomial challenge hpolynomialCanonical hchallenge
  have hout : out = candidate :=
    Result.ok.inj (hevaluate.symm.trans candidateRun)
  subst candidate
  rw [candidateExact]
  apply exact_degree27_from_zero_boundary coordinateFormula
    (storedRound mask round) polynomial
    (ComponentBRealEvaluatorProof.generatedQm31ToExact incoming)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact challenge)
    exact_two_ne_zero hzero
  · have hconstantSet :
        exactConstant polynomial =
          ComponentBRealEvaluatorProof.generatedQm31ToExact updated := by
      rw [hpolynomial]
      simp [exactConstant, ComponentBRealEvaluatorProof.coefficientAt]
    calc
      exactConstant polynomial =
          ComponentBRealEvaluatorProof.generatedQm31ToExact updated := hconstantSet
      _ = ComponentBRealEvaluatorProof.generatedQm31ToExact
            (storedRound mask round).val[0] +
          ComponentBRealEvaluatorProof.generatedQm31ToExact halfValue :=
        updatedExact.2
      _ = exactConstant (storedRound mask round) +
          AspisV5SumcheckCommitment.half *
            ComponentBRealEvaluatorProof.generatedQm31ToExact incoming := by
        rw [halfExact.2]
        rfl
  · intro coefficient
    rw [hpolynomial]
    unfold exactTail ComponentBRealEvaluatorProof.coefficientAt
    apply congrArg ComponentBRealEvaluatorProof.generatedQm31ToExact
    apply Array.getElem_Nat_set_ne
    · simp

/-- Every canonical stored round and canonical challenge admits one authentic
extracted round/evaluator execution, and its exact output is the maintained
`maskStep`.  This removes trace-existence and canonicality as caller
premises for a single round. -/
theorem generated_round_step_exists
    (primitives : ComponentBRealEvaluatorProof.OptimizedPrimitiveCorrespondence)
    (mask : Mask) (round : Fin 10) (incoming challenge : QM31)
    (hincoming : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 incoming)
    (hstored : ComponentBRealEvaluatorProof.CanonicalArray (storedRound mask round))
    (hzero : ExactZeroBoundary (storedRound mask round))
    (hchallenge : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 challenge) :
    ∃ halfValue updated polynomial out,
      ComponentBGenerated.aspis_core.field.QM31.half incoming = .ok halfValue ∧
      ComponentBGenerated.aspis_core.field.QM31.add
          (storedRound mask round).val[0] halfValue = .ok updated ∧
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial
          mask (roundUsize primitives.targetWidth round) incoming =
        .ok (.some polynomial) ∧
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
          polynomial challenge = .ok out ∧
      ComponentBRealEvaluatorProof.CanonicalArray polynomial ∧
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        AspisV5SumcheckCommitment.maskStep
          (ComponentBRealEvaluatorProof.generatedQm31ToExact incoming)
          (exactTail (storedRound mask round))
          (ComponentBRealEvaluatorProof.generatedQm31ToExact challenge) := by
  have hincoming' : ComponentBHalfCombinedProof.CanonicalQM31 incoming := by
    simpa [ComponentBHalfCombinedProof.CanonicalQM31,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
      ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hincoming
  obtain ⟨halfValue, hhalf, hhalfCanonical, _⟩ :=
    ComponentBHalfCombinedProof.generated_qm31_half_doubles_canonical
      incoming hincoming'
  have hhalfCanonical' :
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 halfValue := by
    simpa [ComponentBHalfCombinedProof.CanonicalQM31,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
      ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hhalfCanonical
  have hconstantCanonical :
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        (storedRound mask round).val[0] := hstored ⟨0, by norm_num⟩
  obtain ⟨updated, hadd, hupdatedCanonical, _⟩ :=
    ComponentBRealEvaluatorProof.generated_qm31_add_corresponds
      (storedRound mask round).val[0] halfValue
      hconstantCanonical hhalfCanonical'
  let polynomial : Polynomial := (storedRound mask round).set 0#usize updated
  have hpolynomialCanonical :
      ComponentBRealEvaluatorProof.CanonicalArray polynomial := by
    intro index
    by_cases hindex : index.val = 0
    · have hi : index = ⟨0, by omega⟩ := Fin.ext hindex
      rw [hi]
      simpa [polynomial] using hupdatedCanonical
    · have hvalue :
          ((storedRound mask round).set 0#usize updated).val[index.val] =
            (storedRound mask round).val[index.val] := by
        apply Array.getElem_Nat_set_ne
        exact Ne.symm hindex
      change ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        (((storedRound mask round).set 0#usize updated).val[index.val])
      rw [hvalue]
      exact hstored index
  let roundScalar : Std.Usize := roundUsize primitives.targetWidth round
  have hsome : mask.zero_boundary_rounds.val[roundScalar.val]? =
      some (storedRound mask round) := by
    change mask.zero_boundary_rounds.val[round.val]? = _
    simp [storedRound, round.isLt]
  have hround :
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial
          mask roundScalar incoming =
        .ok (.some polynomial) := by
    simp [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial,
      lift, Array.to_slice, core.slice.Slice.get,
      core.slice.index.Usize.get, hsome, hhalf, hadd,
      Array.index_usize, Array.update, polynomial]
    apply Subtype.ext
    rfl
  obtain ⟨out, hevaluate, houtCanonical, _⟩ :=
    ComponentBRealEvaluatorProof.generated_evaluator_exact_of_optimized_primitives
      primitives polynomial challenge hpolynomialCanonical hchallenge
  refine ⟨halfValue, updated, polynomial, out, hhalf, hadd, hround,
    hevaluate, hpolynomialCanonical, houtCanonical, ?_⟩
  exact generated_round_evaluation_eq_maskStep primitives
    degree27CoordinateFormula_d1e7 mask round incoming halfValue updated
    challenge out polynomial hincoming hstored hzero hchallenge
    hpolynomialCanonical hhalf hadd hround hevaluate

/-- A source-independent induction principle for the maintained affine
recurrence.  Keeping this generic avoids asking the elaborator to normalize
the concrete ten-element `List.ofFn` in one step. -/
private theorem chainContributions_of_steps {K : Type*} [Field K] :
    ∀ {n : ℕ} (states : Fin (n + 1) → K) (contributions : Fin n → K),
      (∀ i : Fin n,
        states i.succ = AspisV5SumcheckCommitment.half * states i.castSucc +
          contributions i) →
      AspisV5SumcheckCommitment.chainContributions
          (states ⟨0, by omega⟩) (List.ofFn contributions) =
        states (Fin.last n) := by
  intro n
  induction n with
  | zero =>
      intro states contributions _
      rfl
  | succ n ih =>
      intro states contributions hstep
      rw [List.ofFn_succ]
      change AspisV5SumcheckCommitment.chainContributions
          (AspisV5SumcheckCommitment.half * states ⟨0, by omega⟩ +
            contributions ⟨0, by omega⟩)
          (List.ofFn (fun i : Fin n ↦ contributions i.succ)) = _
      have hfirst :
          AspisV5SumcheckCommitment.half * states ⟨0, by omega⟩ +
              contributions ⟨0, by omega⟩ =
            states ⟨1, by omega⟩ := by
        exact (hstep ⟨0, by omega⟩).symm
      rw [hfirst]
      have htail : ∀ i : Fin n,
          states i.succ.succ =
            AspisV5SumcheckCommitment.half * states i.succ.castSucc +
              contributions i.succ := by
        intro i
        simpa using hstep i.succ
      have hind := ih
        (fun i : Fin (n + 1) ↦ states i.succ)
        (fun i : Fin n ↦ contributions i.succ)
        htail
      simpa using hind

/-- Ten exact one-round transitions are the maintained fixed-width terminal
covector. -/
theorem ten_maskSteps_eq_terminalCovector
    {K : Type*} [Field K]
    (tails : Fin 10 → Fin 27 → K)
    (point : Fin 10 → K)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : K)
    (h0 : c1 = AspisV5SumcheckCommitment.maskStep c0 (tails 0) (point 0))
    (h1 : c2 = AspisV5SumcheckCommitment.maskStep c1 (tails 1) (point 1))
    (h2 : c3 = AspisV5SumcheckCommitment.maskStep c2 (tails 2) (point 2))
    (h3 : c4 = AspisV5SumcheckCommitment.maskStep c3 (tails 3) (point 3))
    (h4 : c5 = AspisV5SumcheckCommitment.maskStep c4 (tails 4) (point 4))
    (h5 : c6 = AspisV5SumcheckCommitment.maskStep c5 (tails 5) (point 5))
    (h6 : c7 = AspisV5SumcheckCommitment.maskStep c6 (tails 6) (point 6))
    (h7 : c8 = AspisV5SumcheckCommitment.maskStep c7 (tails 7) (point 7))
    (h8 : c9 = AspisV5SumcheckCommitment.maskStep c8 (tails 8) (point 8))
    (h9 : c10 = AspisV5SumcheckCommitment.maskStep c9 (tails 9) (point 9)) :
    c10 = AspisV5SumcheckCommitment.terminalCovector point c0 tails := by
  rw [← AspisV5SumcheckCommitment.tenRoundTerminal_eq_terminalCovector]
  let states : Fin 11 → K := fun i ↦
    match i.val with
    | 0 => c0
    | 1 => c1
    | 2 => c2
    | 3 => c3
    | 4 => c4
    | 5 => c5
    | 6 => c6
    | 7 => c7
    | 8 => c8
    | 9 => c9
    | _ => c10
  let contributions : Fin 10 → K := fun i ↦
    AspisV5SumcheckCommitment.tailEvaluation (tails i) (point i)
  have hstep : ∀ i : Fin 10,
      states i.succ = AspisV5SumcheckCommitment.half * states i.castSucc +
        contributions i := by
    intro i
    fin_cases i
    · change c1 = AspisV5SumcheckCommitment.maskStep c0 (tails 0) (point 0)
      exact h0
    · change c2 = AspisV5SumcheckCommitment.maskStep c1 (tails 1) (point 1)
      exact h1
    · change c3 = AspisV5SumcheckCommitment.maskStep c2 (tails 2) (point 2)
      exact h2
    · change c4 = AspisV5SumcheckCommitment.maskStep c3 (tails 3) (point 3)
      exact h3
    · change c5 = AspisV5SumcheckCommitment.maskStep c4 (tails 4) (point 4)
      exact h4
    · change c6 = AspisV5SumcheckCommitment.maskStep c5 (tails 5) (point 5)
      exact h5
    · change c7 = AspisV5SumcheckCommitment.maskStep c6 (tails 6) (point 6)
      exact h6
    · change c8 = AspisV5SumcheckCommitment.maskStep c7 (tails 7) (point 7)
      exact h7
    · change c9 = AspisV5SumcheckCommitment.maskStep c8 (tails 8) (point 8)
      exact h8
    · change c10 = AspisV5SumcheckCommitment.maskStep c9 (tails 9) (point 9)
      exact h9
  have hchain := chainContributions_of_steps states contributions hstep
  change c10 = AspisV5SumcheckCommitment.chainContributions c0
    (List.ofFn contributions)
  exact hchain.symm

/-- The authentic extracted public evaluator follows its ten stored rounds and
returns the eleventh supplied claim. -/
theorem generated_public_evaluate_returns_claim10
    (primitives : ComponentBRealEvaluatorProof.OptimizedPrimitiveCorrespondence)
    (mask : Mask) (point : Array QM31 10#usize)
    (claims : Array QM31 11#usize)
    (polynomials : Array Polynomial 10#usize)
    (hinitial : claims.val[0] = mask.initial_claim)
    (hround : ∀ i : Fin 10,
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial
          mask (roundUsize primitives.targetWidth i) claims.val[i.val] =
        .ok (.some polynomials.val[i.val]))
    (hevaluate : ∀ i : Fin 10,
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
          polynomials.val[i.val] point.val[i.val] =
        .ok claims.val[i.succ.val]) :
    ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate mask point =
      .ok claims.val[10] := by
  have hroundLiteral (i : Fin 10) (round : Usize)
      (hval : round.val = i.val) :
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial
          mask round claims.val[i.val] = .ok (.some polynomials.val[i.val]) := by
    have heq : round = roundUsize primitives.targetWidth i := by
      apply UScalar.eq_of_val_eq
      simpa using hval
    rw [heq]
    exact hround i
  exact
    ComponentBPublicEvaluateProof.generated_public_evaluate_ten_round_recurrence
      primitives.targetWidth mask point
      polynomials.val[0] polynomials.val[1] polynomials.val[2]
      polynomials.val[3] polynomials.val[4] polynomials.val[5]
      polynomials.val[6] polynomials.val[7] polynomials.val[8]
      polynomials.val[9]
      claims.val[1] claims.val[2] claims.val[3] claims.val[4] claims.val[5]
      claims.val[6] claims.val[7] claims.val[8] claims.val[9] claims.val[10]
      (by simpa [hinitial] using hroundLiteral ⟨0, by omega⟩ 0#usize rfl)
      (hevaluate ⟨0, by omega⟩)
      (hroundLiteral ⟨1, by omega⟩ 1#usize rfl) (hevaluate ⟨1, by omega⟩)
      (hroundLiteral ⟨2, by omega⟩ 2#usize rfl) (hevaluate ⟨2, by omega⟩)
      (hroundLiteral ⟨3, by omega⟩ 3#usize rfl) (hevaluate ⟨3, by omega⟩)
      (hroundLiteral ⟨4, by omega⟩ 4#usize rfl) (hevaluate ⟨4, by omega⟩)
      (hroundLiteral ⟨5, by omega⟩ 5#usize rfl) (hevaluate ⟨5, by omega⟩)
      (hroundLiteral ⟨6, by omega⟩ 6#usize rfl) (hevaluate ⟨6, by omega⟩)
      (hroundLiteral ⟨7, by omega⟩ 7#usize rfl) (hevaluate ⟨7, by omega⟩)
      (hroundLiteral ⟨8, by omega⟩ 8#usize rfl) (hevaluate ⟨8, by omega⟩)
      (hroundLiteral ⟨9, by omega⟩ 9#usize rfl) (hevaluate ⟨9, by omega⟩)

/-- A vector of exact claims satisfying all ten maintained mask transitions
lands at the maintained terminal covector. -/
theorem exact_claim_steps_eq_terminalCovector
    (mask : Mask) (point : Array QM31 10#usize)
    (claims : Array QM31 11#usize)
    (step : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[i.succ.val] =
        AspisV5SumcheckCommitment.maskStep
          (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[i.val])
          (exactTail (storedRound mask i))
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val])) :
    ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[10] =
      AspisV5SumcheckCommitment.terminalCovector
        (fun i : Fin 10 ↦ ComponentBRealEvaluatorProof.generatedQm31ToExact
          point.val[i.val])
        (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[0])
        (fun i ↦ exactTail (storedRound mask i)) := by
  exact ten_maskSteps_eq_terminalCovector (K := ExactQM31)
    (fun i ↦ exactTail (storedRound mask i))
    (fun i : Fin 10 ↦
      ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[0])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[1])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[2])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[3])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[4])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[5])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[6])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[7])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[8])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[9])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[10])
    (step ⟨0, by omega⟩) (step ⟨1, by omega⟩)
    (step ⟨2, by omega⟩) (step ⟨3, by omega⟩)
    (step ⟨4, by omega⟩) (step ⟨5, by omega⟩)
    (step ⟨6, by omega⟩) (step ⟨7, by omega⟩)
    (step ⟨8, by omega⟩) (step ⟨9, by omega⟩)

/-- From canonical sampled round data and a canonical ten-coordinate point,
the authentic extracted public evaluator has a successful result whose exact
value is the maintained terminal covector.  All intermediate half, addition,
round-polynomial, and degree-27 evaluator traces are constructed here. -/
theorem generated_public_evaluate_exists_terminal
    (primitives : ComponentBRealEvaluatorProof.OptimizedPrimitiveCorrespondence)
    (mask : Mask) (point : Array QM31 10#usize)
    (hinitial : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
      mask.initial_claim)
    (hstored : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.CanonicalArray (storedRound mask i))
    (hzero : ∀ i : Fin 10, ExactZeroBoundary (storedRound mask i))
    (hpoint : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 point.val[i.val]) :
    ∃ out,
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate mask point =
          .ok out ∧
        ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
        ComponentBRealEvaluatorProof.generatedQm31ToExact out =
          AspisV5SumcheckCommitment.terminalCovector
            (fun i : Fin 10 ↦
              ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val])
            (ComponentBRealEvaluatorProof.generatedQm31ToExact mask.initial_claim)
            (fun i ↦ exactTail (storedRound mask i)) := by
  obtain ⟨half0, updated0, p0, c1, hh0, ha0, hr0, he0, hp0, hc1, hs0⟩ :=
    generated_round_step_exists primitives mask ⟨0, by omega⟩
      mask.initial_claim point.val[0] hinitial (hstored ⟨0, by omega⟩)
      (hzero ⟨0, by omega⟩) (hpoint ⟨0, by omega⟩)
  obtain ⟨half1, updated1, p1, c2, hh1, ha1, hr1, he1, hp1, hc2, hs1⟩ :=
    generated_round_step_exists primitives mask ⟨1, by omega⟩
      c1 point.val[1] hc1 (hstored ⟨1, by omega⟩)
      (hzero ⟨1, by omega⟩) (hpoint ⟨1, by omega⟩)
  obtain ⟨half2, updated2, p2, c3, hh2, ha2, hr2, he2, hp2, hc3, hs2⟩ :=
    generated_round_step_exists primitives mask ⟨2, by omega⟩
      c2 point.val[2] hc2 (hstored ⟨2, by omega⟩)
      (hzero ⟨2, by omega⟩) (hpoint ⟨2, by omega⟩)
  obtain ⟨half3, updated3, p3, c4, hh3, ha3, hr3, he3, hp3, hc4, hs3⟩ :=
    generated_round_step_exists primitives mask ⟨3, by omega⟩
      c3 point.val[3] hc3 (hstored ⟨3, by omega⟩)
      (hzero ⟨3, by omega⟩) (hpoint ⟨3, by omega⟩)
  obtain ⟨half4, updated4, p4, c5, hh4, ha4, hr4, he4, hp4, hc5, hs4⟩ :=
    generated_round_step_exists primitives mask ⟨4, by omega⟩
      c4 point.val[4] hc4 (hstored ⟨4, by omega⟩)
      (hzero ⟨4, by omega⟩) (hpoint ⟨4, by omega⟩)
  obtain ⟨half5, updated5, p5, c6, hh5, ha5, hr5, he5, hp5, hc6, hs5⟩ :=
    generated_round_step_exists primitives mask ⟨5, by omega⟩
      c5 point.val[5] hc5 (hstored ⟨5, by omega⟩)
      (hzero ⟨5, by omega⟩) (hpoint ⟨5, by omega⟩)
  obtain ⟨half6, updated6, p6, c7, hh6, ha6, hr6, he6, hp6, hc7, hs6⟩ :=
    generated_round_step_exists primitives mask ⟨6, by omega⟩
      c6 point.val[6] hc6 (hstored ⟨6, by omega⟩)
      (hzero ⟨6, by omega⟩) (hpoint ⟨6, by omega⟩)
  obtain ⟨half7, updated7, p7, c8, hh7, ha7, hr7, he7, hp7, hc8, hs7⟩ :=
    generated_round_step_exists primitives mask ⟨7, by omega⟩
      c7 point.val[7] hc7 (hstored ⟨7, by omega⟩)
      (hzero ⟨7, by omega⟩) (hpoint ⟨7, by omega⟩)
  obtain ⟨half8, updated8, p8, c9, hh8, ha8, hr8, he8, hp8, hc9, hs8⟩ :=
    generated_round_step_exists primitives mask ⟨8, by omega⟩
      c8 point.val[8] hc8 (hstored ⟨8, by omega⟩)
      (hzero ⟨8, by omega⟩) (hpoint ⟨8, by omega⟩)
  obtain ⟨half9, updated9, p9, c10, hh9, ha9, hr9, he9, hp9, hc10, hs9⟩ :=
    generated_round_step_exists primitives mask ⟨9, by omega⟩
      c9 point.val[9] hc9 (hstored ⟨9, by omega⟩)
      (hzero ⟨9, by omega⟩) (hpoint ⟨9, by omega⟩)
  have run :=
    ComponentBPublicEvaluateProof.generated_public_evaluate_ten_round_recurrence
      primitives.targetWidth mask point p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
      c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
      hr0 he0 hr1 he1 hr2 he2 hr3 he3 hr4 he4
      hr5 he5 hr6 he6 hr7 he7 hr8 he8 hr9 he9
  refine ⟨c10, run, hc10, ?_⟩
  exact ten_maskSteps_eq_terminalCovector (K := ExactQM31)
    (fun i ↦ exactTail (storedRound mask i))
    (fun i : Fin 10 ↦
      ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val])
    (ComponentBRealEvaluatorProof.generatedQm31ToExact mask.initial_claim)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c1)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c2)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c3)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c4)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c5)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c6)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c7)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c8)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c9)
    (ComponentBRealEvaluatorProof.generatedQm31ToExact c10)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9

/-- Current owning-crate field extraction discharges the optimized primitive
bundle, leaving only the recorded 64-bit extraction target and the semantic
input invariants for the deterministic public evaluator. -/
theorem generated_public_evaluate_exists_terminal_current_field
    (targetWidth : System.Platform.numBits = 64)
    (mask : Mask) (point : Array QM31 10#usize)
    (hinitial : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
      mask.initial_claim)
    (hstored : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.CanonicalArray (storedRound mask i))
    (hzero : ∀ i : Fin 10, ExactZeroBoundary (storedRound mask i))
    (hpoint : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 point.val[i.val]) :
    ∃ out,
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate mask point =
          .ok out ∧
        ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
        ComponentBRealEvaluatorProof.generatedQm31ToExact out =
          AspisV5SumcheckCommitment.terminalCovector
            (fun i : Fin 10 ↦
              ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val])
            (ComponentBRealEvaluatorProof.generatedQm31ToExact mask.initial_claim)
            (fun i ↦ exactTail (storedRound mask i)) := by
  exact generated_public_evaluate_exists_terminal
    (ComponentBRealEvaluatorProof.optimizedPrimitiveCorrespondence_current_field
      targetWidth)
    mask point hinitial hstored hzero hpoint

/-- The authentic extracted public ten-round evaluator returns the maintained
terminal covector, provided each sampled stored round carries the exact
zero-boundary invariant and the extracted field primitives use their proved
exact semantics. -/
theorem generated_public_evaluate_eq_terminalCovector
    (primitives : ComponentBRealEvaluatorProof.OptimizedPrimitiveCorrespondence)
    (mask : Mask) (point : Array QM31 10#usize)
    (claims : Array QM31 11#usize)
    (halfValues updated : Array QM31 10#usize)
    (polynomials : Array Polynomial 10#usize)
    (hinitial : claims.val[0] = mask.initial_claim)
    (hclaims : ∀ i : Fin 11,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 claims.val[i.val])
    (hpoints : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 point.val[i.val])
    (hstored : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.CanonicalArray (storedRound mask i))
    (hzero : ∀ i : Fin 10, ExactZeroBoundary (storedRound mask i))
    (hpolynomials : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.CanonicalArray polynomials.val[i.val])
    (hhalf : ∀ i : Fin 10,
      ComponentBGenerated.aspis_core.field.QM31.half claims.val[i.val] =
        .ok halfValues.val[i.val])
    (hadd : ∀ i : Fin 10,
      ComponentBGenerated.aspis_core.field.QM31.add
          (storedRound mask i).val[0] halfValues.val[i.val] =
        .ok updated.val[i.val])
    (hround : ∀ i : Fin 10,
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.round_polynomial
          mask (roundUsize primitives.targetWidth i) claims.val[i.val] =
        .ok (.some polynomials.val[i.val]))
    (hevaluate : ∀ i : Fin 10,
      ComponentBGenerated.aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
          polynomials.val[i.val] point.val[i.val] =
        .ok claims.val[i.succ.val]) :
    ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate mask point =
        .ok claims.val[10] ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[10] =
        AspisV5SumcheckCommitment.terminalCovector
          (fun i : Fin 10 ↦ ComponentBRealEvaluatorProof.generatedQm31ToExact
            point.val[i.val])
          (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[0])
          (fun i ↦ exactTail (storedRound mask i)) := by
  have step : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[i.succ.val] =
        AspisV5SumcheckCommitment.maskStep
          (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[i.val])
          (exactTail (storedRound mask i))
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val]) := by
    intro i
    exact generated_round_evaluation_eq_maskStep primitives
      degree27CoordinateFormula_d1e7
      mask i claims.val[i.val] halfValues.val[i.val] updated.val[i.val]
      point.val[i.val] claims.val[i.succ.val] polynomials.val[i.val]
      (hclaims ⟨i.val, by omega⟩) (hstored i) (hzero i) (hpoints i)
      (hpolynomials i) (hhalf i) (hadd i) (hround i) (hevaluate i)
  exact ⟨generated_public_evaluate_returns_claim10 primitives mask point claims
      polynomials hinitial hround hevaluate,
    exact_claim_steps_eq_terminalCovector mask point claims step⟩

/-- Concrete tooth: omitting the sampler's derived constant coefficient is
observable in one round. With one nonzero tail coefficient and challenge zero,
the uncorrected degree-27 evaluation is zero, whereas `maskStep` includes the
required `-tail / 2` correction and is nonzero. -/
theorem omitted_zero_boundary_constant_changes_round :
    let tail : Fin AspisV5SumcheckCommitment.tailCount → ℚ :=
      fun coefficient ↦
      if coefficient.val = 0 then 1 else 0
    (∑ coefficient : Fin AspisV5SumcheckCommitment.tailCount,
        tail coefficient * (0 : ℚ) ^ (coefficient.val + 1)) ≠
      AspisV5SumcheckCommitment.maskStep (0 : ℚ) tail 0 := by
  dsimp
  have hpow (coefficient : Fin AspisV5SumcheckCommitment.tailCount) :
      (0 : ℚ) ^ (coefficient.val + 1) = 0 := by
    apply zero_pow
    omega
  simp_rw [hpow, mul_zero]
  simp only [Finset.sum_const_zero]
  unfold AspisV5SumcheckCommitment.maskStep
    AspisV5SumcheckCommitment.tailEvaluation
    AspisV5SumcheckCommitment.half
  simp only [mul_zero, zero_add]
  rw [Finset.sum_eq_single
    (⟨0, by norm_num [AspisV5SumcheckCommitment.tailCount]⟩ :
      Fin AspisV5SumcheckCommitment.tailCount)]
  · norm_num
  · intro coefficient _ hne
    have hval : coefficient.val ≠ 0 := by
      intro hzero
      apply hne
      apply Fin.ext
      exact hzero
    simp [hval]
  · simp

#print axioms generated_round_evaluation_eq_maskStep
#print axioms generated_round_step_exists
#print axioms ten_maskSteps_eq_terminalCovector
#print axioms generated_public_evaluate_returns_claim10
#print axioms exact_claim_steps_eq_terminalCovector
#print axioms generated_public_evaluate_exists_terminal
#print axioms generated_public_evaluate_exists_terminal_current_field
#print axioms generated_public_evaluate_eq_terminalCovector
#print axioms omitted_zero_boundary_constant_changes_round

end ComponentBMaintainedTerminalBridge
