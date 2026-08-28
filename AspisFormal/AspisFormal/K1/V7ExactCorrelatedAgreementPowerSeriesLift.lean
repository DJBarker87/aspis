import AspisFormal.K1.V7ExactCorrelatedAgreementFunctionField
import AspisFormal.K1.V7ExactCorrelatedAgreementHensel

/-!
# Shifted-X Hensel lift of a fixed exact V7 branch

This file maps `R(X,Y,Z)` into `L⟦T⟧[Y]` by `X ↦ x₀ + T`, where
`L = QM31(Z)[Y]/(H)`.  Constant coefficient is proved to be literal
specialization at `X=x₀`; consequently the simple branch root constructed in
the function-field module satisfies the exact hypotheses of the non-monic
Hensel theorem.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementHensel
open AspisV5ComponentCQM31TowerExact

noncomputable section

def localBranchBaseMap
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] :
    K →+* LocalBranchField factor :=
  (AdjoinRoot.of (localFactorOverRational factor)).comp
    ((algebraMap (Polynomial K) (ChallengeRationalField K)).comp C)

/-- The transcendental challenge `Z`, embedded in the local branch field. -/
def localBranchChallenge
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] :
    LocalBranchField factor :=
  AdjoinRoot.of (localFactorOverRational factor)
    (algebraMap (Polynomial K) (ChallengeRationalField K) X)

/-- Substitute `X = x₀ + T` in an innermost polynomial coefficient. -/
def shiftedXCoefficientHom
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] (x₀ : K) :
    Polynomial K →+* PowerSeries (LocalBranchField factor) :=
  Polynomial.eval₂RingHom
    ((PowerSeries.C : LocalBranchField factor →+*
      PowerSeries (LocalBranchField factor)).comp
        (localBranchBaseMap factor))
    (PowerSeries.C (localBranchBaseMap factor x₀) + PowerSeries.X)

/-- Substitute `Z` by its rational-function-field element and `X=x₀+T`. -/
def localCoefficientPowerSeriesHom
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] (x₀ : K) :
    Polynomial (Polynomial K) →+*
      PowerSeries (LocalBranchField factor) :=
  Polynomial.eval₂RingHom (shiftedXCoefficientHom factor x₀)
    (PowerSeries.C (localBranchChallenge factor))

/-- The global branch in the shifted-X complete local ring. -/
def liftedGlobalFactor
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))] :
    Polynomial (PowerSeries (LocalBranchField localFactor)) :=
  globalFactor.map (localCoefficientPowerSeriesHom localFactor x₀)

/-- Taking the constant coefficient after `X↦x₀+T` is exactly evaluation
at `X=x₀`. -/
theorem constantCoeff_comp_shiftedXCoefficientHom
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] (x₀ : K) :
    (PowerSeries.constantCoeff (R := LocalBranchField factor)).comp
        (shiftedXCoefficientHom factor x₀) =
      (localBranchBaseMap factor).comp (Polynomial.evalRingHom x₀) := by
  apply Polynomial.ringHom_ext
  · intro value
    simp [shiftedXCoefficientHom, localBranchBaseMap]
  · simp [shiftedXCoefficientHom, localBranchBaseMap]

/-- Constant coefficient of the full `X,Z` coefficient map is the fixed
`X=x₀` specialization followed by the two function-field embeddings. -/
theorem constantCoeff_comp_localCoefficientPowerSeriesHom
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] (x₀ : K) :
    (PowerSeries.constantCoeff (R := LocalBranchField factor)).comp
        (localCoefficientPowerSeriesHom factor x₀) =
      (AdjoinRoot.of (localFactorOverRational factor)).comp
        ((algebraMap (Polynomial K) (ChallengeRationalField K)).comp
          (evaluateInnerVariable x₀)) := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    simpa [localCoefficientPowerSeriesHom, localBranchBaseMap,
      evaluateInnerVariable] using congrArg
        (fun hom : Polynomial K →+* LocalBranchField factor =>
          hom coefficient)
        (constantCoeff_comp_shiftedXCoefficientHom factor x₀)
  · simp [localCoefficientPowerSeriesHom, localBranchChallenge,
      evaluateInnerVariable]

/-- Evaluation of the lifted branch at a constant candidate commutes with
constant coefficient and is exactly evaluation of `R(x₀,Y,Z)` in `L`. -/
theorem constantCoeff_liftedGlobalFactor_eval_C
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (candidate : LocalBranchField localFactor) :
    PowerSeries.constantCoeff
        ((liftedGlobalFactor globalFactor x₀ localFactor).eval
          (PowerSeries.C candidate)) =
      (((specializeEvaluationPoint x₀ globalFactor).map
        (algebraMap (Polynomial QM31Exact)
          (ChallengeRationalField QM31Exact))).map
        (AdjoinRoot.of (localFactorOverRational localFactor))).eval
          candidate := by
  unfold liftedGlobalFactor
  rw [Polynomial.eval_map, Polynomial.hom_eval₂]
  rw [constantCoeff_comp_localCoefficientPowerSeriesHom]
  simp only [PowerSeries.constantCoeff_C]
  rw [Polynomial.eval_map, Polynomial.eval₂_map]
  exact (Polynomial.eval₂_map (evaluateInnerVariable x₀)
    ((AdjoinRoot.of (localFactorOverRational localFactor)).comp
      (algebraMap (Polynomial QM31Exact)
        (ChallengeRationalField QM31Exact))) candidate).symm

/-- The same commuting square for the outer `Y` derivative. -/
theorem constantCoeff_liftedGlobalFactor_derivative_eval_C
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (candidate : LocalBranchField localFactor) :
    PowerSeries.constantCoeff
        ((liftedGlobalFactor globalFactor x₀ localFactor).derivative.eval
          (PowerSeries.C candidate)) =
      ((((specializeEvaluationPoint x₀ globalFactor).derivative).map
        (algebraMap (Polynomial QM31Exact)
          (ChallengeRationalField QM31Exact))).map
        (AdjoinRoot.of (localFactorOverRational localFactor))).eval
          candidate := by
  have specializedDerivative :
      specializeEvaluationPoint x₀ globalFactor.derivative =
        (specializeEvaluationPoint x₀ globalFactor).derivative := by
    change globalFactor.derivative.map (evaluateInnerVariable x₀) =
      (globalFactor.map (evaluateInnerVariable x₀)).derivative
    rw [Polynomial.derivative_map]
  calc
    PowerSeries.constantCoeff
        ((liftedGlobalFactor globalFactor x₀ localFactor).derivative.eval
          (PowerSeries.C candidate)) =
        PowerSeries.constantCoeff
          ((liftedGlobalFactor globalFactor.derivative x₀ localFactor).eval
            (PowerSeries.C candidate)) := by
      simp only [liftedGlobalFactor, Polynomial.derivative_map]
    _ = (((specializeEvaluationPoint x₀ globalFactor.derivative).map
          (algebraMap (Polynomial QM31Exact)
            (ChallengeRationalField QM31Exact))).map
          (AdjoinRoot.of (localFactorOverRational localFactor))).eval
            candidate :=
      constantCoeff_liftedGlobalFactor_eval_C globalFactor.derivative x₀
        localFactor candidate
    _ = _ := by rw [specializedDerivative]

/-- Exact existence of the power-series lift attached to a fixed smooth local
branch.  Its constant coefficient is the literal adjoined root of `H`. -/
theorem exists_exactV7_fixedBranch_powerSeriesRoot
    (globalFactor : TrivariatePolynomial QM31Exact)
    (x₀ : QM31Exact)
    (certificateAtPoint :
      (Polynomial.Bivariate.swap
        (separabilityCertificate globalFactor)).eval (C x₀) ≠ 0)
    (localFactor : BivariatePolynomial QM31Exact)
    (localFactorMem : localFactor ∈
      bivariatePrimeFactors (specializeEvaluationPoint x₀ globalFactor))
    (localFactorPositive : 0 < localFactor.natDegree) :
    let parent := specializeEvaluationPoint x₀ globalFactor
    let parentNeZero : parent ≠ 0 := by
      intro parentZero
      have noFactor : bivariatePrimeFactors parent = 0 := by
        simp [bivariatePrimeFactors, parentZero]
      rw [noFactor] at localFactorMem
      simpa using localFactorMem
    letI : Fact (Irreducible (localFactorOverRational localFactor)) :=
      ⟨localFactorOverRational_irreducible parent localFactor parentNeZero
        localFactorMem localFactorPositive⟩
    ∃ root : PowerSeries (LocalBranchField localFactor),
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root ∧
        PowerSeries.constantCoeff root =
          AdjoinRoot.root (localFactorOverRational localFactor) := by
  dsimp only
  let parent := specializeEvaluationPoint x₀ globalFactor
  have parentNeZero : parent ≠ 0 := by
    intro parentZero
    have noFactor : bivariatePrimeFactors parent = 0 := by
      simp [bivariatePrimeFactors, parentZero]
    rw [noFactor] at localFactorMem
    simpa using localFactorMem
  letI : Fact (Irreducible (localFactorOverRational localFactor)) :=
    ⟨localFactorOverRational_irreducible parent localFactor parentNeZero
      localFactorMem localFactorPositive⟩
  let branchRoot := AdjoinRoot.root (localFactorOverRational localFactor)
  apply exists_powerSeries_root_of_simple_constant_root
    (liftedGlobalFactor globalFactor x₀ localFactor) branchRoot
  · rw [constantCoeff_liftedGlobalFactor_eval_C]
    exact (localBranchRoot_isRoot_parent parent localFactor parentNeZero
      localFactorMem localFactorPositive).eq_zero
  · rw [constantCoeff_liftedGlobalFactor_derivative_eval_C]
    simpa only [Polynomial.IsRoot] using
      (localBranchRoot_not_isRoot_parentDerivative globalFactor x₀
        certificateAtPoint localFactor localFactorMem localFactorPositive)

#print axioms constantCoeff_comp_localCoefficientPowerSeriesHom
#print axioms constantCoeff_liftedGlobalFactor_eval_C
#print axioms exists_exactV7_fixedBranch_powerSeriesRoot

end

end AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
