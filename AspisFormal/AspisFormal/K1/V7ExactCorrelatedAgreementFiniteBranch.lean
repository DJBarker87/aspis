import AspisFormal.K1.V7ExactCorrelatedAgreementHenselSpecialization
import AspisFormal.K1.V7ExactCorrelatedAgreementFactorBudgets

/-!
# Finite polynomial extraction from the fixed Hensel branch

This file contains the exact truncation step from BCH+25/BCIKS: after the
regular zero count kills the coefficients above the released message degree
and below the interpolation `X` bound, the truncated fixed branch is shown to
be an exact polynomial root.  No characteristic-zero or analytic convergence
argument is used.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementFiniteBranch

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementHensel
open AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics
open AspisK1.V7ExactCorrelatedAgreementHenselSpecialization
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementHenselWeights
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Polynomial evaluation modulo `T^order` only sees the input series modulo
`T^order`. -/
theorem trunc_eval_coe_trunc
    {R : Type*} [CommRing R]
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (order : Nat) :
    PowerSeries.trunc order
        (polynomial.eval (PowerSeries.trunc order series : PowerSeries R)) =
      PowerSeries.trunc order (polynomial.eval series) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp only [Polynomial.eval_add, map_add, leftInduction, rightInduction]
  | monomial exponent coefficient =>
      simp only [Polynomial.eval_monomial]
      calc
        PowerSeries.trunc order
            (coefficient *
              (PowerSeries.trunc order series : PowerSeries R) ^ exponent) =
          PowerSeries.trunc order
            ((PowerSeries.trunc order coefficient : PowerSeries R) *
              (PowerSeries.trunc order series : PowerSeries R) ^ exponent) := by
            rw [PowerSeries.trunc_trunc_mul]
        _ = PowerSeries.trunc order
            (coefficient *
              (PowerSeries.trunc order series : PowerSeries R) ^ exponent) := by
            rw [PowerSeries.trunc_trunc_mul]
        _ = PowerSeries.trunc order
            (coefficient *
              (PowerSeries.trunc order
                ((PowerSeries.trunc order series : PowerSeries R) ^ exponent) :
                  PowerSeries R)) := by
            rw [PowerSeries.trunc_mul_trunc]
        _ = PowerSeries.trunc order
            (coefficient *
              (PowerSeries.trunc order (series ^ exponent) : PowerSeries R)) := by
            rw [PowerSeries.trunc_trunc_pow]
        _ = PowerSeries.trunc order (coefficient * series ^ exponent) := by
            rw [PowerSeries.trunc_mul_trunc]

/-- A root remains a root modulo `T^order` after literal truncation. -/
theorem trunc_eval_coe_trunc_eq_zero_of_isRoot
    {R : Type*} [CommRing R]
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (order : Nat)
    (root : polynomial.IsRoot series) :
    PowerSeries.trunc order
        (polynomial.eval (PowerSeries.trunc order series : PowerSeries R)) = 0 := by
  rw [trunc_eval_coe_trunc polynomial series order, root.eq_zero, map_zero]

/-! ## The finite shifted polynomial before power-series completion -/

/-- Literal Taylor shift `X ↦ x₀+T`, still in the polynomial ring over
the fixed local function field. -/
def shiftedXPolynomialHom
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))]
    (x₀ : QM31Exact) :
    QM31Exact[X] →+* Polynomial (LocalBranchField factor) :=
  (Polynomial.mapRingHom (localBranchBaseMap factor)).comp
    (Polynomial.taylorAlgHom x₀).toRingHom

/-- Substitute the transcendental challenge into a bivariate coefficient,
then perform the polynomial Taylor shift in the evaluation variable. -/
def localCoefficientPolynomialHom
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))]
    (x₀ : QM31Exact) :
    BivariatePolynomial QM31Exact →+* Polynomial (LocalBranchField factor) :=
  Polynomial.eval₂RingHom (shiftedXPolynomialHom factor x₀)
    (C (localBranchChallenge factor))

/-- Evaluate a polynomial in the challenge indeterminate inside the fixed
local algebraic function field. -/
def localBranchChallengeMap
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))] :
    QM31Exact[X] →+* LocalBranchField factor :=
  (AdjoinRoot.of (localFactorOverRational factor)).comp
    (algebraMap (Polynomial QM31Exact) (ChallengeRationalField QM31Exact))

/-- The same coefficient substitution after literally swapping `X` and
`Z`: first embed every `Z` coefficient into the function field, then Taylor
shift the now-outer `X`. -/
def reorderedLocalCoefficientPolynomialHom
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))]
    (x₀ : QM31Exact) :
    BivariatePolynomial QM31Exact →+* Polynomial (LocalBranchField factor) :=
  (Polynomial.taylorAlgHom (localBranchBaseMap factor x₀)).toRingHom.comp
    ((Polynomial.mapRingHom (localBranchChallengeMap factor)).comp
      (Polynomial.Bivariate.swap (R := QM31Exact)).toRingHom)

theorem localCoefficientPolynomialHom_eq_reordered
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))]
    (x₀ : QM31Exact) :
    localCoefficientPolynomialHom factor x₀ =
      reorderedLocalCoefficientPolynomialHom factor x₀ := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    induction coefficient using Polynomial.induction_on' with
    | add left right leftInduction rightInduction =>
        simp only [map_add, leftInduction, rightInduction]
    | monomial exponent value =>
        unfold localCoefficientPolynomialHom
          reorderedLocalCoefficientPolynomialHom
        simp only [RingHom.comp_apply]
        simp [shiftedXPolynomialHom,
          localBranchChallengeMap, localBranchBaseMap,
          Polynomial.taylor_monomial, Polynomial.Bivariate.swap_C]
  · unfold localCoefficientPolynomialHom
      reorderedLocalCoefficientPolynomialHom
    simp only [RingHom.comp_apply]
    simp [localBranchChallengeMap,
      localBranchChallenge, Polynomial.taylor_C,
      Polynomial.Bivariate.swap_Y]

theorem coeff_trivariateXYPolynomial
    (globalFactor : TrivariatePolynomial QM31Exact) (yExponent : Nat) :
    (trivariateXYPolynomial QM31Exact globalFactor).coeff yExponent =
      Polynomial.Bivariate.swap (globalFactor.coeff yExponent) := by
  apply Polynomial.ext
  intro xExponent
  unfold trivariateXYPolynomial
  rw [coeff_coeff_bivariate_swap]
  change ((Polynomial.Bivariate.swap
      (globalFactor.map
        (Polynomial.Bivariate.swap (R := QM31Exact)).toRingHom)).coeff
        xExponent).coeff yExponent = _
  rw [coeff_coeff_bivariate_swap, Polynomial.coeff_map]
  rfl

theorem localBranchChallengeMap_injective
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))] :
    Function.Injective (localBranchChallengeMap factor) := by
  exact (AdjoinRoot.of (localFactorOverRational factor)).injective.comp
    (IsFractionRing.injective (Polynomial QM31Exact)
      (ChallengeRationalField QM31Exact))

theorem localCoefficientPolynomialHom_injective
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))]
    (x₀ : QM31Exact) :
    Function.Injective (localCoefficientPolynomialHom factor x₀) := by
  rw [localCoefficientPolynomialHom_eq_reordered]
  exact (Polynomial.taylorEquiv
      (localBranchBaseMap factor x₀)).injective.comp
    ((Polynomial.map_injective (localBranchChallengeMap factor)
      (localBranchChallengeMap_injective factor)).comp
        (Polynomial.Bivariate.swap (R := QM31Exact)).injective)

theorem natDegree_localCoefficientPolynomialHom
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))]
    (x₀ : QM31Exact) (polynomial : BivariatePolynomial QM31Exact) :
    (localCoefficientPolynomialHom factor x₀ polynomial).natDegree =
      (Polynomial.Bivariate.swap polynomial).natDegree := by
  rw [localCoefficientPolynomialHom_eq_reordered]
  change (Polynomial.taylor (localBranchBaseMap factor x₀)
      ((Polynomial.Bivariate.swap polynomial).map
        (localBranchChallengeMap factor))).natDegree = _
  rw [Polynomial.natDegree_taylor]
  exact Polynomial.natDegree_map_eq_of_injective
    (localBranchChallengeMap_injective factor)
      (Polynomial.Bivariate.swap polynomial)

/-- The fixed global irreducible branch as a polynomial in `Y`, with
polynomial-in-`T` coefficients over its algebraic function field. -/
def polynomialLiftedGlobalFactor
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))] :
    Polynomial (Polynomial (LocalBranchField localFactor)) :=
  globalFactor.map (localCoefficientPolynomialHom localFactor x₀)

theorem localBivariateWeight_polynomialLiftedGlobalFactor_le
    (curveDegree : Nat)
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))] :
    localBivariateWeight curveDegree
        (polynomialLiftedGlobalFactor globalFactor x₀ localFactor) ≤
      trivariateXYWeight curveDegree globalFactor := by
  apply localBivariateWeight_le_of_coeff
  intro yExponent yMem
  have mappedCoefficientNeZero :
      localCoefficientPolynomialHom localFactor x₀
          (globalFactor.coeff yExponent) ≠ 0 := by
    simpa [polynomialLiftedGlobalFactor, Polynomial.mem_support_iff] using
      (Polynomial.mem_support_iff.mp yMem)
  have originalCoefficientNeZero : globalFactor.coeff yExponent ≠ 0 := by
    intro coefficientZero
    apply mappedCoefficientNeZero
    rw [coefficientZero, map_zero]
  have reorderedMem : yExponent ∈
      (trivariateXYPolynomial QM31Exact globalFactor).support := by
    rw [Polynomial.mem_support_iff, coeff_trivariateXYPolynomial]
    simpa using (Polynomial.Bivariate.swap
      (R := QM31Exact)).injective.ne originalCoefficientNeZero
  rw [polynomialLiftedGlobalFactor, Polynomial.coeff_map,
    natDegree_localCoefficientPolynomialHom,
    ← coeff_trivariateXYPolynomial]
  exact coeff_weight_le_localBivariateWeight curveDegree
    (trivariateXYPolynomial QM31Exact globalFactor) yExponent reorderedMem

theorem coe_shiftedXPolynomialHom
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))]
    (x₀ : QM31Exact) (polynomial : QM31Exact[X]) :
    (shiftedXPolynomialHom factor x₀ polynomial :
        PowerSeries (LocalBranchField factor)) =
      shiftedXCoefficientHom factor x₀ polynomial := by
  rw [shiftedXCoefficientHom_eq_coe_taylor]
  rfl

theorem coe_comp_localCoefficientPolynomialHom
    (factor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational factor))]
    (x₀ : QM31Exact) :
    (Polynomial.coeToPowerSeries.ringHom (R := LocalBranchField factor)).comp
        (localCoefficientPolynomialHom factor x₀) =
      localCoefficientPowerSeriesHom factor x₀ := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    simpa [localCoefficientPolynomialHom, localCoefficientPowerSeriesHom] using
      coe_shiftedXPolynomialHom factor x₀ coefficient
  · simp [localCoefficientPolynomialHom, localCoefficientPowerSeriesHom]

theorem map_coe_polynomialLiftedGlobalFactor
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))] :
    (polynomialLiftedGlobalFactor globalFactor x₀ localFactor).map
        (Polynomial.coeToPowerSeries.ringHom
          (R := LocalBranchField localFactor)) =
      liftedGlobalFactor globalFactor x₀ localFactor := by
  unfold polynomialLiftedGlobalFactor liftedGlobalFactor
  rw [Polynomial.map_map, coe_comp_localCoefficientPolynomialHom]

/-- Substitution of a degree-`k` polynomial into a bivariate polynomial has
degree bounded by its literal `(1,k)` weighted degree. -/
theorem natDegree_eval_le_localBivariateWeight
    {R : Type*} [CommRing R] [IsDomain R]
    (curveDegree : Nat) (polynomial : BivariatePolynomial R)
    (value : R[X]) (valueDegree : value.natDegree ≤ curveDegree) :
    (polynomial.eval value).natDegree ≤
      localBivariateWeight curveDegree polynomial := by
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent exponentMem
  by_cases coefficientZero : polynomial.coeff exponent = 0
  · simp [coefficientZero]
  · have exponentMemSupport : exponent ∈ polynomial.support :=
      Polynomial.mem_support_iff.mpr coefficientZero
    calc
      (polynomial.coeff exponent * value ^ exponent).natDegree ≤
          (polynomial.coeff exponent).natDegree +
            (value ^ exponent).natDegree := Polynomial.natDegree_mul_le
      _ ≤ (polynomial.coeff exponent).natDegree +
          exponent * value.natDegree := Nat.add_le_add_left
            Polynomial.natDegree_pow_le _
      _ ≤ (polynomial.coeff exponent).natDegree +
          exponent * curveDegree := by gcongr
      _ ≤ localBivariateWeight curveDegree polynomial := by
        simpa [Nat.mul_comm] using
          coeff_weight_le_localBivariateWeight curveDegree polynomial exponent
            exponentMemSupport

theorem eval_coe_polynomialLiftedGlobalFactor
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (value : Polynomial (LocalBranchField localFactor)) :
    (liftedGlobalFactor globalFactor x₀ localFactor).eval
        (value : PowerSeries (LocalBranchField localFactor)) =
      (((polynomialLiftedGlobalFactor globalFactor x₀ localFactor).eval value :
        Polynomial (LocalBranchField localFactor)) :
          PowerSeries (LocalBranchField localFactor)) := by
  calc
    (liftedGlobalFactor globalFactor x₀ localFactor).eval
        (value : PowerSeries (LocalBranchField localFactor)) =
      (((polynomialLiftedGlobalFactor globalFactor x₀ localFactor).map
          (Polynomial.coeToPowerSeries.ringHom
            (R := LocalBranchField localFactor))).eval
        (value : PowerSeries (LocalBranchField localFactor))) := by
          rw [map_coe_polynomialLiftedGlobalFactor]
    _ = _ := by
      rw [Polynomial.eval_map]
      symm
      simpa using Polynomial.hom_eval₂
        (polynomialLiftedGlobalFactor globalFactor x₀ localFactor)
        (RingHom.id (Polynomial (LocalBranchField localFactor)))
        (Polynomial.coeToPowerSeries.ringHom
          (R := LocalBranchField localFactor)) value

/-- Once all coefficients between the released degree and the interpolation
`X` bound have vanished, the finite truncation is an exact root.  The proof
uses only polynomial degree: evaluation is zero modulo `T^xBound`, while its
actual degree is strictly below `xBound`. -/
theorem polynomialTruncation_isRoot
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (curveDegree xBound : Nat)
    (globalWeightLt :
      trivariateXYWeight curveDegree globalFactor < xBound)
    (truncationDegree :
      (PowerSeries.trunc xBound root).natDegree ≤ curveDegree) :
    (polynomialLiftedGlobalFactor globalFactor x₀ localFactor).IsRoot
      (PowerSeries.trunc xBound root) := by
  let finiteRoot := PowerSeries.trunc xBound root
  let finiteFactor := polynomialLiftedGlobalFactor globalFactor x₀ localFactor
  have completedEvaluation := eval_coe_polynomialLiftedGlobalFactor
    globalFactor x₀ localFactor finiteRoot
  have moduloZero := trunc_eval_coe_trunc_eq_zero_of_isRoot
    (liftedGlobalFactor globalFactor x₀ localFactor) root xBound rootEquation
  have finiteDegree : (finiteFactor.eval finiteRoot).natDegree < xBound := by
    exact (natDegree_eval_le_localBivariateWeight curveDegree finiteFactor
      finiteRoot truncationDegree |>.trans
        (localBivariateWeight_polynomialLiftedGlobalFactor_le curveDegree
          globalFactor x₀ localFactor)).trans_lt globalWeightLt
  rw [completedEvaluation,
    PowerSeries.trunc_coe_eq_self finiteDegree] at moduloZero
  exact moduloZero

theorem natDegree_trunc_le_of_coeff_eq_zero
    {R : Type*} [Semiring R] (series : PowerSeries R)
    (degree bound : Nat)
    (coefficientZero : ∀ order, degree < order → order < bound →
      PowerSeries.coeff order series = 0) :
    (PowerSeries.trunc bound series).natDegree ≤ degree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro order orderLarge
  rw [PowerSeries.coeff_trunc]
  split_ifs with orderBelow
  · exact coefficientZero order orderLarge orderBelow
  · rfl

theorem polynomialTruncation_isRoot_of_gap_coefficients_zero
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (curveDegree xBound : Nat)
    (globalWeightLt :
      trivariateXYWeight curveDegree globalFactor < xBound)
    (gapZero : ∀ order, curveDegree < order → order < xBound →
      PowerSeries.coeff order root = 0) :
    (polynomialLiftedGlobalFactor globalFactor x₀ localFactor).IsRoot
      (PowerSeries.trunc xBound root) := by
  apply polynomialTruncation_isRoot globalFactor x₀ localFactor root
    rootEquation curveDegree xBound globalWeightLt
  exact natDegree_trunc_le_of_coeff_eq_zero root curveDegree xBound gapZero

theorem fixedBranchRoot_eq_coe_truncation_of_gap_coefficients_zero
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (derivativeModuloVariableNeZero : PowerSeries.constantCoeff
      ((liftedGlobalFactor globalFactor x₀ localFactor).derivative.eval
        (PowerSeries.C
          (AdjoinRoot.root (localFactorOverRational localFactor)))) ≠ 0)
    (curveDegree xBound : Nat)
    (globalWeightLt :
      trivariateXYWeight curveDegree globalFactor < xBound)
    (gapZero : ∀ order, curveDegree < order → order < xBound →
      PowerSeries.coeff order root = 0) :
    root = (PowerSeries.trunc xBound root :
      PowerSeries (LocalBranchField localFactor)) := by
  have finitePolynomialRoot :=
    polynomialTruncation_isRoot_of_gap_coefficients_zero globalFactor x₀
      localFactor root rootEquation curveDegree xBound globalWeightLt gapZero
  have finitePowerSeriesRoot :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot
        (PowerSeries.trunc xBound root :
          PowerSeries (LocalBranchField localFactor)) := by
    rw [Polynomial.IsRoot,
      eval_coe_polynomialLiftedGlobalFactor globalFactor x₀ localFactor,
      finitePolynomialRoot.eq_zero]
    rfl
  have xBoundPositive : 0 < xBound := by omega
  apply powerSeries_root_unique_of_simple_constant_root
      (liftedGlobalFactor globalFactor x₀ localFactor)
      (AdjoinRoot.root (localFactorOverRational localFactor))
      derivativeModuloVariableNeZero root
      (PowerSeries.trunc xBound root :
        PowerSeries (LocalBranchField localFactor))
      rootEquation finitePowerSeriesRoot rootConstant
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos xBoundPositive]
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using rootConstant

/-- Terminal fixed-branch extraction from challenge-dependent candidates.
Every challenge may carry a different polynomial candidate.  What remains
fixed is the globally pigeonholed irreducible pair and its Hensel root.  The
explicit simple-root, pole-avoidance, and derivative hypotheses are retained;
there is no characteristic-zero specialization shortcut. -/
theorem fixedBranchRoot_eq_coe_truncation_of_many_specializations
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (localFactorPositive : 0 < localFactor.natDegree)
    (ell localBound parentBound : Nat)
    (ellLeParent : ell ≤ parentBound)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (globalCoefficientBound : ∀ exponent ∈ globalFactor.support,
      (globalFactor.coeff exponent).natDegree + ell * exponent ≤ parentBound)
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (etaNeZero : regularizedHenselDerivative globalFactor x₀ localFactor ≠ 0)
    (derivativeModuloVariableNeZero : PowerSeries.constantCoeff
      ((liftedGlobalFactor globalFactor x₀ localFactor).derivative.eval
        (PowerSeries.C
          (AdjoinRoot.root (localFactorOverRational localFactor)))) ≠ 0)
    (curveDegree xBound : Nat)
    (globalWeightLt :
      trivariateXYWeight curveDegree globalFactor < xBound)
    (challenges : Finset QM31Exact)
    (candidate : QM31Exact → QM31Exact[X])
    (localRoot : ∀ z ∈ challenges,
      localFactor.eval₂ (Polynomial.evalRingHom z)
        ((candidate z).eval x₀) = 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidateHom z (candidate z) globalFactor = 0)
    (simple : ∀ z ∈ challenges,
      SimpleSpecializedRoot globalFactor x₀ z (candidate z))
    (notPole : ∀ z ∈ challenges,
      z ∉ localPoleChallengeSet localFactor)
    (candidateDegree : ∀ z ∈ challenges,
      (candidate z).natDegree ≤ curveDegree)
    (tooMany : ∀ order, curveDegree < order → order < xBound →
      localFactor.natDegree *
          ((localBound + ell - ell * localFactor.natDegree) +
            henselDenominatorExponent order *
              ((parentBound - ell) + (globalFactor.natDegree - 1) *
                (localBound - ell * localFactor.natDegree))) <
        challenges.card) :
    root = (PowerSeries.trunc xBound root :
      PowerSeries (LocalBranchField localFactor)) := by
  apply fixedBranchRoot_eq_coe_truncation_of_gap_coefficients_zero
    globalFactor x₀ localFactor root rootEquation rootConstant
      derivativeModuloVariableNeZero curveDegree xBound globalWeightLt
  intro order curveDegreeLt orderLt
  apply coeff_fixedBranchRoot_eq_zero_of_many_specializations
    globalFactor globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive ell localBound parentBound ellLeParent
      localCoefficientBound globalCoefficientBound root rootEquation
      rootConstant etaNeZero challenges candidate localRoot candidateRoot
      simple notPole order
  · intro z zMem
    exact (candidateDegree z zMem).trans_lt curveDegreeLt
  · exact tooMany order curveDegreeLt orderLt

#print axioms trunc_eval_coe_trunc
#print axioms trunc_eval_coe_trunc_eq_zero_of_isRoot
#print axioms map_coe_polynomialLiftedGlobalFactor
#print axioms natDegree_eval_le_localBivariateWeight
#print axioms polynomialTruncation_isRoot
#print axioms polynomialTruncation_isRoot_of_gap_coefficients_zero
#print axioms fixedBranchRoot_eq_coe_truncation_of_gap_coefficients_zero
#print axioms fixedBranchRoot_eq_coe_truncation_of_many_specializations

end

end AspisK1.V7ExactCorrelatedAgreementFiniteBranch
