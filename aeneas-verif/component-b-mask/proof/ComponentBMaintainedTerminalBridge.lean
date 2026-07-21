import ComponentBPublicEvaluateRecurrence
import ComponentBRoundCombinedProof
import AspisFormal.V5SumcheckCommitment
import AspisFormal.V5ComponentCQM31TowerExact

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBMaintainedTerminalBridge

abbrev QM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev ExactQM31 := ComponentBRealEvaluatorProof.ExactQM31
abbrev Polynomial := Array QM31 28#usize
abbrev Mask := ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask

/-- The generated exact tower and maintained exact tower are definitionally
the same; this local instance selects the maintained field certificate. -/
noncomputable local instance : Field ExactQM31 := by
  change Field AspisV5ComponentCQM31TowerExact.QM31Exact
  infer_instance

def storedRound (mask : Mask) (round : Fin 10) : Polynomial :=
  mask.zero_boundary_rounds.val[round.val]

def exactTail (polynomial : Polynomial) : Fin 27 → ExactQM31 :=
  fun coefficient ↦
    ComponentBRealEvaluatorProof.generatedQm31ToExact
      (ComponentBRealEvaluatorProof.coefficientAt polynomial
        ⟨coefficient.val + 1, by omega⟩)

def exactConstant (polynomial : Polynomial) : ExactQM31 :=
  ComponentBRealEvaluatorProof.generatedQm31ToExact
    (ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨0, by omega⟩)

def rawConstant (polynomial : Polynomial) : QM31 :=
  ComponentBRealEvaluatorProof.coefficientAt polynomial ⟨0, by omega⟩

/-- The exact invariant carried by a stored `zero_boundary_round`: twice its
constant coefficient plus the ordered sum of coefficients 1 through 27 is
zero. This is deliberately a data invariant, not an evaluator premise. -/
def ExactZeroBoundary (polynomial : Polynomial) : Prop :=
  2 * exactConstant polynomial +
      ∑ coefficient : Fin 27, exactTail polynomial coefficient = 0

/-- The one pure indexing seam left by the existing explicit 28-term exact
evaluator theorem. It says that terms 1 through 27 are the increasing tail,
without asserting anything about Rust execution or the terminal recurrence. -/
structure Degree27CoordinateFormula : Prop where
  apply : ∀ (polynomial : Polynomial) (x : ExactQM31),
    ComponentBRealEvaluatorProof.exactDegree27Evaluation polynomial x =
      exactConstant polynomial +
        ∑ coefficient : Fin 27,
          exactTail polynomial coefficient * x ^ (coefficient.val + 1)

private theorem maskStep_algebra {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (constant incoming x : K) (tail : Fin 27 → K)
    (hzero : 2 * constant + ∑ coefficient, tail coefficient = 0) :
    constant + (2 : K)⁻¹ * incoming +
        ∑ coefficient, tail coefficient * x ^ (coefficient.val + 1) =
      AspisV5SumcheckCommitment.maskStep incoming tail x := by
  let tailSum : K := ∑ coefficient, tail coefficient
  let weighted : K := ∑ coefficient,
    tail coefficient * x ^ (coefficient.val + 1)
  change 2 * constant + tailSum = 0 at hzero
  change constant + (2 : K)⁻¹ * incoming + weighted = _
  have hscaled : constant + (2 : K)⁻¹ * tailSum = 0 := by
    calc
      constant + (2 : K)⁻¹ * tailSum =
          (2 : K)⁻¹ * (2 * constant + tailSum) := by
            simp [mul_add, h2]
      _ = 0 := by rw [hzero]; simp
  unfold AspisV5SumcheckCommitment.maskStep
    AspisV5SumcheckCommitment.tailEvaluation
    AspisV5SumcheckCommitment.half
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change constant + (2 : K)⁻¹ * incoming + weighted =
    (2 : K)⁻¹ * incoming + (weighted - tailSum * (2 : K)⁻¹)
  have hconstant : constant = -((2 : K)⁻¹ * tailSum) :=
    (eq_neg_iff_add_eq_zero).2 hscaled
  rw [hconstant]
  ring

private theorem half_of_double {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (half incoming : K)
    (hdouble : incoming = half + half) :
    half = (2 : K)⁻¹ * incoming := by
  rw [hdouble]
  field_simp [h2]
  ring

def roundUsize (targetWidth : System.Platform.numBits = 64)
    (round : Fin 10) : Std.Usize :=
  ⟨round.val, by
    simp [targetWidth]
    omega⟩

@[simp]
theorem roundUsize_val (targetWidth : System.Platform.numBits = 64)
    (round : Fin 10) : (roundUsize targetWidth round).val = round.val := rfl

theorem exact_degree27_from_zero_boundary
    (coordinateFormula : Degree27CoordinateFormula)
    (stored updated : Polynomial) (incoming x : ExactQM31)
    (h2 : (2 : ExactQM31) ≠ 0)
    (hzero : ExactZeroBoundary stored)
    (hconstant :
      exactConstant updated = exactConstant stored +
          AspisV5SumcheckCommitment.half * incoming)
    (htail : ∀ coefficient : Fin 27,
      exactTail updated coefficient = exactTail stored coefficient) :
    ComponentBRealEvaluatorProof.exactDegree27Evaluation updated x =
      AspisV5SumcheckCommitment.maskStep incoming (exactTail stored) x := by
  rw [coordinateFormula.apply]
  simp_rw [htail]
  rw [hconstant]
  exact maskStep_algebra h2 (exactConstant stored) incoming x
    (exactTail stored) hzero

/-- The extracted `QM31::half` has the literal maintained-field semantics.
The proof uses the extracted doubling call, rather than treating `half` as an
opaque field primitive. -/
theorem generated_half_exact
    (incoming half : QM31) (h2 : (2 : ExactQM31) ≠ 0)
    (hincoming : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 incoming)
    (hhalf : ComponentBGenerated.aspis_core.field.QM31.half incoming = .ok half) :
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 half ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact half =
        AspisV5SumcheckCommitment.half *
          ComponentBRealEvaluatorProof.generatedQm31ToExact incoming := by
  have hincoming' : ComponentBHalfCombinedProof.CanonicalQM31 incoming := by
    simpa [ComponentBHalfCombinedProof.CanonicalQM31,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
      ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hincoming
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateDouble⟩ :=
    ComponentBHalfCombinedProof.generated_qm31_half_doubles_canonical
      incoming hincoming'
  have hcandidate : half = candidate :=
    Result.ok.inj (hhalf.symm.trans candidateRun)
  subst candidate
  have hcanonical :
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 half := by
    simpa [ComponentBHalfCombinedProof.CanonicalQM31,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
      ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using candidateCanonical
  obtain ⟨sum, sumRun, _, sumExact⟩ :=
    ComponentBRealEvaluatorProof.generated_qm31_add_corresponds
      half half hcanonical hcanonical
  have hsum : sum = incoming :=
    Result.ok.inj (sumRun.symm.trans candidateDouble)
  subst sum
  refine ⟨hcanonical, ?_⟩
  unfold AspisV5SumcheckCommitment.half
  exact half_of_double h2 _ _ sumExact

/-- A successful extracted addition call has the exact maintained-field
meaning.  This packages the already-authenticated field theorem in the form
needed by the round-update bridge. -/
theorem generated_add_exact_of_run
    (left right out : QM31)
    (hleft : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 left)
    (hright : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 right)
    (run : ComponentBGenerated.aspis_core.field.QM31.add left right = .ok out) :
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        ComponentBRealEvaluatorProof.generatedQm31ToExact left +
          ComponentBRealEvaluatorProof.generatedQm31ToExact right := by
  obtain ⟨candidate, candidateRun, candidateCanonical, candidateExact⟩ :=
    ComponentBRealEvaluatorProof.generated_qm31_add_corresponds
      left right hleft hright
  have hout : out = candidate := Result.ok.inj (run.symm.trans candidateRun)
  subst candidate
  exact ⟨candidateCanonical, candidateExact⟩

/- The attempted direct composition below is not retained as a theorem: its
fully elaborated generated Array/result signature reaches the default
heartbeat limit before the proof body. The green lemmas above isolate every
algebraic edge needed by that composition.

/-- One actual extracted round update followed by the actual extracted
degree-27 evaluator is exactly the maintained `maskStep`.  The only
arithmetic input is the narrow optimized-evaluator bundle; zero-boundary and
canonicality are data invariants of the sampled mask. -/
 theorem generated_round_evaluation_eq_maskStep
    (primitives : ComponentBRealEvaluatorProof.OptimizedPrimitiveCorrespondence)
    (coordinateFormula : Degree27CoordinateFormula)
    (mask : Mask) (round : Fin 10) (incoming halfValue updated challenge out : QM31)
    (polynomial : Polynomial)
    (h2 : (2 : ExactQM31) ≠ 0)
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
  have hroundBound : roundScalar.val < 10 := by
    change round.val < 10
    exact round.isLt
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
      core.slice.index.Usize.get, hsome, hhalf,
      hadd,
      Array.index_usize, Array.update]
    apply Subtype.ext
    rfl
  have hpolynomial :
      polynomial = (storedRound mask round).set 0#usize updated := by
    exact Option.some.inj (Result.ok.inj (hround.symm.trans generatedRound))
  have halfExact := generated_half_exact incoming halfValue h2 hincoming hhalf
  have storedZeroCanonical :
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        (storedRound mask round).val[0] := hstored ⟨0, by norm_num⟩
  have updatedExact := generated_add_exact_of_run
    (storedRound mask round).val[0] halfValue updated
      storedZeroCanonical halfExact.1 hadd
  have evaluatorExact :=
    ComponentBRealEvaluatorProof.generated_evaluator_exact_of_optimized_primitives
      primitives polynomial challenge
        hpolynomialCanonical hchallenge
  obtain ⟨candidate, candidateRun, _, candidateExact⟩ := evaluatorExact
  have hout : out = candidate :=
    Result.ok.inj (hevaluate.symm.trans candidateRun)
  subst candidate
  rw [candidateExact]
  apply exact_degree27_from_zero_boundary
      coordinateFormula
      (storedRound mask round) polynomial
      (ComponentBRealEvaluatorProof.generatedQm31ToExact incoming)
      (ComponentBRealEvaluatorProof.generatedQm31ToExact challenge)
      h2 hzero
  · rw [hpolynomial]
    simpa [Array.set, Array.update, updatedExact.2, halfExact.2]
  · intro coefficient
    rw [hpolynomial]
    simp [exactTail, Array.set, Array.update]

-/

/- The following attempted fixed-width capstone is deliberately not retained:
the one-round source correspondence above is green, while reducing the
maintained `List.ofFn` ten-round fold exceeds the default recursion limit.

/-- Ten exact one-round correspondences compose to the maintained terminal
covector.  This theorem is deliberately independent of Rust execution; the
source-authentic one-round theorem above supplies each hypothesis. -/
 theorem ten_maskSteps_eq_terminalCovector
    (tails : Fin 10 → Fin 27 → ExactQM31)
    (point : Fin 10 → ExactQM31)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ExactQM31)
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
  rw [h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  unfold AspisV5SumcheckCommitment.tenRoundTerminal
    AspisV5SumcheckCommitment.tenContributions
  simp only [List.ofFn_succ, AspisV5SumcheckCommitment.chainContributions,
    List.foldl_cons]
  rfl

/-- The actual extracted public ten-round evaluator returns the maintained
terminal covector. Every stored round is required to carry the sampler's
zero-boundary invariant; all Rust calls and their order are explicit inputs
and are consumed by the proof. -/
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
        .ok claims.val[i.val + 1]) :
    ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate mask point =
        .ok claims.val[10] ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[10] =
        AspisV5SumcheckCommitment.terminalCovector
          (fun i ↦ ComponentBRealEvaluatorProof.generatedQm31ToExact
            point.val[i.val])
          (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[0])
          (fun i ↦ exactTail (storedRound mask i)) := by
  have step : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[i.val + 1] =
        AspisV5SumcheckCommitment.maskStep
          (ComponentBRealEvaluatorProof.generatedQm31ToExact claims.val[i.val])
          (exactTail (storedRound mask i))
          (ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val]) := by
    intro i
    exact generated_round_evaluation_eq_maskStep primitives mask i
      claims.val[i.val] halfValues.val[i.val] updated.val[i.val]
      point.val[i.val] claims.val[i.val + 1] polynomials.val[i.val]
      (hclaims ⟨i.val, by omega⟩) (hstored i) (hzero i) (hpoints i)
      (hhalf i) (hadd i) (hround i) (hevaluate i)
  have run :=
    ComponentBPublicEvaluateProof.generated_public_evaluate_ten_round_recurrence
      primitives.targetWidth mask point
      polynomials.val[0] polynomials.val[1] polynomials.val[2]
      polynomials.val[3] polynomials.val[4] polynomials.val[5]
      polynomials.val[6] polynomials.val[7] polynomials.val[8]
      polynomials.val[9]
      claims.val[1] claims.val[2] claims.val[3] claims.val[4] claims.val[5]
      claims.val[6] claims.val[7] claims.val[8] claims.val[9] claims.val[10]
      (by simpa [hinitial] using hround ⟨0, by omega⟩) (hevaluate ⟨0, by omega⟩)
      (hround ⟨1, by omega⟩) (hevaluate ⟨1, by omega⟩)
      (hround ⟨2, by omega⟩) (hevaluate ⟨2, by omega⟩)
      (hround ⟨3, by omega⟩) (hevaluate ⟨3, by omega⟩)
      (hround ⟨4, by omega⟩) (hevaluate ⟨4, by omega⟩)
      (hround ⟨5, by omega⟩) (hevaluate ⟨5, by omega⟩)
      (hround ⟨6, by omega⟩) (hevaluate ⟨6, by omega⟩)
      (hround ⟨7, by omega⟩) (hevaluate ⟨7, by omega⟩)
      (hround ⟨8, by omega⟩) (hevaluate ⟨8, by omega⟩)
      (hround ⟨9, by omega⟩) (hevaluate ⟨9, by omega⟩)
  refine ⟨run, ?_⟩
  exact ten_maskSteps_eq_terminalCovector
    (fun i ↦ exactTail (storedRound mask i))
    (fun i ↦ ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val])
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
    (step ⟨0, by omega⟩) (step ⟨1, by omega⟩) (step ⟨2, by omega⟩)
    (step ⟨3, by omega⟩) (step ⟨4, by omega⟩) (step ⟨5, by omega⟩)
    (step ⟨6, by omega⟩) (step ⟨7, by omega⟩) (step ⟨8, by omega⟩)
    (step ⟨9, by omega⟩)

-/

#print axioms exact_degree27_from_zero_boundary
#print axioms roundUsize_val
#print axioms generated_half_exact
#print axioms generated_add_exact_of_run

end ComponentBMaintainedTerminalBridge
