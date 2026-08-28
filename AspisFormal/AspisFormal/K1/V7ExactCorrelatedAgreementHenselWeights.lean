import AspisFormal.K1.V7ExactCorrelatedAgreementHenselRecurrence
import AspisFormal.K1.V7ExactCorrelatedAgreementRegularHensel
import AspisFormal.K1.V7ExactCorrelatedAgreementFactorBudgets
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Weight-safe denominator for the exact V7 Hensel lift

The older BCIKS Appendix A presentation writes the smaller denominator
`xi = W^(d-2) * dR/dY`.  Its printed weight argument informally identifies
the ceiling weight of the integral generator `T` with `deg W + ell`, which
need not be an equality when the leading coefficient does not saturate the
weighted-degree ceiling.

For the kernel proof we instead retain the fully regular derivative

`eta = W^(d-1) * dR/dY`.

This costs no asymptotic or released-parameter slack: the uniform cleared
coefficient is `W * eta^(2t-1) * alpha_t`, whose branch weight is bounded by
the generator ceiling plus `(2t-1)` times the weight of `eta`.  This file
establishes the derivative and `eta` bounds without any characteristic-zero
assumption.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementHenselWeights

open scoped BigOperators
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementRegularEvaluation
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Formal differentiation lowers the literal `(ell,1)` weighted degree by
`ell`.  The proof is valid in finite characteristic: if a natural scalar
vanishes modulo the characteristic then that derivative coefficient simply
does not belong to the support. -/
theorem derivative_coefficientWeight_le
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K)
    (ell bound : Nat)
    (coefficientBound : ∀ exponent ∈ polynomial.support,
      (polynomial.coeff exponent).natDegree + ell * exponent ≤ bound) :
    ∀ exponent ∈ polynomial.derivative.support,
      (polynomial.derivative.coeff exponent).natDegree + ell * exponent ≤
        bound - ell := by
  intro exponent exponentMem
  have derivativeCoefficientNeZero :
      polynomial.derivative.coeff exponent ≠ 0 :=
    Polynomial.mem_support_iff.mp exponentMem
  rw [Polynomial.coeff_derivative] at derivativeCoefficientNeZero ⊢
  have originalCoefficientNeZero : polynomial.coeff (exponent + 1) ≠ 0 := by
    exact fun coefficientZero => derivativeCoefficientNeZero (by
      rw [coefficientZero, zero_mul])
  have scalarNeZero :
      ((exponent : Polynomial K) + 1) ≠ 0 := by
    exact fun scalarZero => derivativeCoefficientNeZero (by
      rw [scalarZero, mul_zero])
  have originalMem : exponent + 1 ∈ polynomial.support :=
    Polynomial.mem_support_iff.mpr originalCoefficientNeZero
  have originalBound := coefficientBound (exponent + 1) originalMem
  have productDegree :
      (polynomial.coeff (exponent + 1) *
          ((exponent : Polynomial K) + 1)).natDegree =
        (polynomial.coeff (exponent + 1)).natDegree := by
    rw [Polynomial.natDegree_mul originalCoefficientNeZero scalarNeZero]
    have castSuccessor :
        ((exponent : Polynomial K) + 1) =
          ((exponent + 1 : Nat) : Polynomial K) := by
      norm_cast
    rw [castSuccessor, Polynomial.natDegree_natCast]
    omega
  rw [productDegree]
  rw [Nat.mul_succ] at originalBound
  omega

/-- Weight of the division-free derivative `eta = W^(d-1) dR/dY` in the
actual integral local quotient. -/
theorem integralBranchIteratedWeight_regularizedHenselDerivative_le
    {K : Type*} [Field K]
    (globalFactor : TrivariatePolynomial K) (x₀ : K)
    (localFactor : BivariatePolynomial K) (localFactorNeZero : localFactor ≠ 0)
    (ell localBound parentBound : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (parentCoefficientBound : ∀ exponent ∈
        (specializeEvaluationPoint x₀ globalFactor).support,
      ((specializeEvaluationPoint x₀ globalFactor).coeff exponent).natDegree +
        ell * exponent ≤ parentBound) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (regularizedHenselDerivative globalFactor x₀ localFactor) ≤
      (parentBound - ell) + (globalFactor.natDegree - 1) *
        (localBound - ell * localFactor.natDegree) := by
  let parent := specializeEvaluationPoint x₀ globalFactor
  have derivativeDegreeLe : parent.derivative.natDegree ≤
      globalFactor.natDegree - 1 :=
    specializedDerivative_natDegree_le_global_sub_one globalFactor x₀
  have derivativeBound := derivative_coefficientWeight_le parent ell
    parentBound parentCoefficientBound
  exact integralBranchIteratedWeight_regularizedBranchEvaluation_le
    localFactor parent.derivative localFactorNeZero
      (globalFactor.natDegree - 1) ell localBound (parentBound - ell)
      derivativeDegreeLe localCoefficientBound derivativeBound

/-- The constant Hensel coefficient is cleared by one literal leading
coefficient: `W * alpha_0 = T`.  This is an identity in the fixed function
field, not a specialization statement. -/
theorem leading_mul_constantBranchRoot
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational localFactor))] :
    regularCoefficientMap localFactor localFactor.leadingCoeff *
        AdjoinRoot.root (localFactorOverRational localFactor) =
      integralBranchToFunctionField localFactor
        (AdjoinRoot.root (integralLocalFactor localFactor)) := by
  rw [integralBranchToFunctionField_root]
  rfl

/-! ## Literal shifted-X coefficients -/

/-- The released shifted coefficient map is exactly the polynomial Taylor
expansion embedded into power series.  Hasse derivatives are used, so this
identity is valid without division by factorials in the QM31
characteristic. -/
theorem shiftedXCoefficientHom_eq_coe_taylor
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (x₀ : K) (polynomial : Polynomial K) :
    shiftedXCoefficientHom localFactor x₀ polynomial =
      ((Polynomial.taylor x₀ polynomial).map
        (localBranchBaseMap localFactor) :
          Polynomial (LocalBranchField localFactor)) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      rw [map_add, leftInduction, rightInduction, map_add]
      rw [Polynomial.map_add]
      exact (Polynomial.coe_add
        ((Polynomial.taylor x₀ left).map (localBranchBaseMap localFactor))
        ((Polynomial.taylor x₀ right).map
          (localBranchBaseMap localFactor))).symm
  | monomial exponent coefficient =>
      change Polynomial.eval₂
          ((PowerSeries.C : LocalBranchField localFactor →+*
            PowerSeries (LocalBranchField localFactor)).comp
              (localBranchBaseMap localFactor))
          (PowerSeries.C (localBranchBaseMap localFactor x₀) +
            PowerSeries.X)
          (Polynomial.monomial exponent coefficient) = _
      rw [Polynomial.eval₂_monomial, RingHom.comp_apply,
        Polynomial.taylor_monomial, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X,
        Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
        Polynomial.coe_add, Polynomial.coe_X]
      rw [add_comm]
      rw [Polynomial.map_C, Polynomial.coe_C]

/-- Consequently every shifted coefficient is the image of the exact Hasse
derivative evaluation in the base field. -/
theorem coeff_shiftedXCoefficientHom
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (x₀ : K) (polynomial : Polynomial K) (order : Nat) :
    PowerSeries.coeff order
        (shiftedXCoefficientHom localFactor x₀ polynomial) =
      localBranchBaseMap localFactor
        ((Polynomial.hasseDeriv order polynomial).eval x₀) := by
  rw [shiftedXCoefficientHom_eq_coe_taylor]
  rw [Polynomial.coeff_coe, Polynomial.coeff_map,
    Polynomial.taylor_coeff]

/-- The literal `Z`-polynomial whose coefficients are the order-`s` Hasse
derivatives in the shifted evaluation variable. -/
noncomputable def shiftedChallengeCoefficient
    {K : Type*} [Field K] (x₀ : K) (order : Nat)
    (polynomial : BivariatePolynomial K) : Polynomial K :=
  polynomial.sum fun challengeExponent coefficient =>
    Polynomial.monomial challengeExponent
      ((Polynomial.hasseDeriv order coefficient).eval x₀)

@[simp] theorem shiftedChallengeCoefficient_add
    {K : Type*} [Field K] (x₀ : K) (order : Nat)
    (left right : BivariatePolynomial K) :
    shiftedChallengeCoefficient x₀ order (left + right) =
      shiftedChallengeCoefficient x₀ order left +
        shiftedChallengeCoefficient x₀ order right := by
  unfold shiftedChallengeCoefficient
  rw [Polynomial.sum_add_index]
  · intro exponent
    simp
  · intro exponent leftCoefficient rightCoefficient
    simp only [map_add, Polynomial.eval_add]

@[simp] theorem shiftedChallengeCoefficient_monomial
    {K : Type*} [Field K] (x₀ : K) (order challengeExponent : Nat)
    (coefficient : Polynomial K) :
    shiftedChallengeCoefficient x₀ order
        (Polynomial.monomial challengeExponent coefficient) =
      Polynomial.monomial challengeExponent
        ((Polynomial.hasseDeriv order coefficient).eval x₀) := by
  unfold shiftedChallengeCoefficient
  rw [Polynomial.sum_monomial_index]
  simp

theorem coeff_shiftedChallengeCoefficient
    {K : Type*} [Field K] (x₀ : K) (order : Nat)
    (polynomial : BivariatePolynomial K) (challengeExponent : Nat) :
    (shiftedChallengeCoefficient x₀ order polynomial).coeff
        challengeExponent =
      (Polynomial.hasseDeriv order
        (polynomial.coeff challengeExponent)).eval x₀ := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      rw [shiftedChallengeCoefficient_add, Polynomial.coeff_add,
        leftInduction, rightInduction, Polynomial.coeff_add, map_add,
        Polynomial.eval_add]
  | monomial exponent coefficient =>
      rw [shiftedChallengeCoefficient_monomial]
      by_cases same : exponent = challengeExponent
      · subst exponent
        simp
      · simp [Polynomial.coeff_monomial, same]

/-- Shifting the ignored evaluation variable cannot increase challenge
degree. -/
theorem shiftedChallengeCoefficient_natDegree_le
    {K : Type*} [Field K] (x₀ : K) (order : Nat)
    (polynomial : BivariatePolynomial K) :
    (shiftedChallengeCoefficient x₀ order polynomial).natDegree ≤
      polynomial.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro challengeExponent exponentLarge
  rw [coeff_shiftedChallengeCoefficient]
  have coefficientZero : polynomial.coeff challengeExponent = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt exponentLarge
  rw [coefficientZero, map_zero, Polynomial.eval_zero]

theorem shiftedChallengeCoefficient_weight_le
    {K : Type*} [Field K] (x₀ : K) (order ell outerExponent bound : Nat)
    (polynomial : BivariatePolynomial K)
    (originalBound : polynomial.natDegree + ell * outerExponent ≤ bound) :
    (shiftedChallengeCoefficient x₀ order polynomial).natDegree +
        ell * outerExponent ≤ bound := by
  exact (Nat.add_le_add_right
    (shiftedChallengeCoefficient_natDegree_le x₀ order polynomial)
      (ell * outerExponent)).trans originalBound

/-- The concrete regular representative of a shifted coefficient inherits
the exact challenge-degree bound of the released trivariate coefficient. -/
theorem integralBranchIteratedWeight_shiftedCoefficient_le
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (x₀ : K) (order : Nat) (polynomial : BivariatePolynomial K) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (AdjoinRoot.of (integralLocalFactor localFactor)
          (shiftedChallengeCoefficient x₀ order polynomial)) ≤
      polynomial.natDegree := by
  exact (integralBranchIteratedWeight_of_le_natDegree localFactor
    localFactorNeZero ell localBound localCoefficientBound
      (shiftedChallengeCoefficient x₀ order polynomial)).trans
    (shiftedChallengeCoefficient_natDegree_le x₀ order polynomial)

/-- Every coefficient of the full released `X ↦ x₀+T, Z ↦ Z` map is
the image of a concrete polynomial in the regular coefficient ring. -/
theorem coeff_localCoefficientPowerSeriesHom
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (x₀ : K) (polynomial : BivariatePolynomial K) (order : Nat) :
    PowerSeries.coeff order
        (localCoefficientPowerSeriesHom localFactor x₀ polynomial) =
      regularCoefficientMap localFactor
        (shiftedChallengeCoefficient x₀ order polynomial) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      rw [map_add, map_add, leftInduction, rightInduction,
        shiftedChallengeCoefficient_add, map_add]
  | monomial challengeExponent coefficient =>
      change PowerSeries.coeff order
        (Polynomial.eval₂
          (shiftedXCoefficientHom localFactor x₀)
          (PowerSeries.C (localBranchChallenge localFactor))
          (Polynomial.monomial challengeExponent coefficient)) = _
      rw [Polynomial.eval₂_monomial]
      rw [show PowerSeries.C (localBranchChallenge localFactor) ^
          challengeExponent =
        PowerSeries.C (localBranchChallenge localFactor ^
          challengeExponent) by simp]
      rw [PowerSeries.coeff_mul_C, coeff_shiftedXCoefficientHom,
        shiftedChallengeCoefficient_monomial]
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      rfl

/-- Coefficients of the shifted fixed global branch therefore have literal
regular `K[Z]` representatives, uniformly in both the outer `Y` exponent and
the shifted `X` order. -/
theorem coeff_liftedGlobalFactor_coefficient
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (yExponent order : Nat) :
    PowerSeries.coeff order
        ((liftedGlobalFactor globalFactor x₀ localFactor).coeff yExponent) =
      regularCoefficientMap localFactor
        (shiftedChallengeCoefficient x₀ order
          (globalFactor.coeff yExponent)) := by
  unfold liftedGlobalFactor
  rw [Polynomial.coeff_map]
  exact coeff_localCoefficientPowerSeriesHom localFactor x₀
    (globalFactor.coeff yExponent) order

/-! ## Integral representatives of literal power-series convolutions -/

/-- The division-free representative of one full coefficient of
`series ^ power`.  Each root coefficient is replaced by its already-cleared
regular representative; the residual powers of `leading` and `eta` are the
literal natural-number differences certified by the antidiagonal exponent
bound. -/
noncomputable def regularClearedPowerCoefficient
    {O : Type*} [CommRing O]
    (leading eta : O) (cleared : Nat → O)
    (power order etaPower : Nat) : O :=
  ∑ parts ∈ (Finset.range power).finsuppAntidiag order,
    leading ^ (power - (Finset.range power).card) *
      eta ^ (etaPower - ∑ index ∈ Finset.range power,
        henselDenominatorExponent (parts index)) *
        ∏ index ∈ Finset.range power, cleared (parts index)

/-- Mapping the regular convolution representative to the branch field gives
exactly `leading^power * eta^etaPower` times the corresponding power-series
coefficient.  This is an equality, not a divisibility assertion, and uses no
cancellation. -/
theorem map_regularClearedPowerCoefficient
    {O F : Type*} [CommRing O] [CommRing F]
    (mapToField : O →+* F) (leading eta : O) (cleared : Nat → O)
    (series : PowerSeries F) (power order etaPower : Nat)
    (clearedImage : ∀ parts ∈
        (Finset.range power).finsuppAntidiag order,
      ∀ index ∈ Finset.range power,
      mapToField (cleared (parts index)) =
        mapToField leading *
          mapToField eta ^ henselDenominatorExponent (parts index) *
            PowerSeries.coeff (parts index) series)
    (exponentBound : ∀ parts ∈
        (Finset.range power).finsuppAntidiag order,
      ∑ index ∈ Finset.range power,
          henselDenominatorExponent (parts index) ≤ etaPower) :
    mapToField (regularClearedPowerCoefficient leading eta cleared
        power order etaPower) =
      mapToField leading ^ power * mapToField eta ^ etaPower *
        PowerSeries.coeff order (series ^ power) := by
  classical
  unfold regularClearedPowerCoefficient
  rw [map_sum, PowerSeries.coeff_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro parts partsMem
  simp only [map_mul, map_pow, map_prod]
  have cardLe : (Finset.range power).card ≤ power := by simp
  have clearedProduct :
      ∏ index ∈ Finset.range power, mapToField (cleared (parts index)) =
        ∏ index ∈ Finset.range power,
          (mapToField leading *
            mapToField eta ^ henselDenominatorExponent (parts index)) *
              PowerSeries.coeff (parts index) series := by
    apply Finset.prod_congr rfl
    intro index indexMem
    exact clearedImage parts partsMem index indexMem
  rw [clearedProduct]
  have clearedIdentity := clear_hensel_product_denominators
    (Finset.range power) (mapToField leading) (mapToField eta)
    (fun index => henselDenominatorExponent (parts index))
    (fun index => PowerSeries.coeff (parts index) series)
    power etaPower cardLe (exponentBound parts partsMem)
  simpa only [Finset.card_range] using clearedIdentity.symm

/-- The supported version omits exactly the zero convolution products.  It
is the form used for powers of the zero-constant tail, where the two-positive-
part saving is available only on nonzero summands. -/
noncomputable def regularClearedSupportedPowerCoefficient
    {O F : Type*} [CommRing O] [CommRing F] [DecidableEq F]
    (leading eta : O) (cleared : Nat → O) (series : PowerSeries F)
    (power order etaPower : Nat) : O :=
  ∑ parts ∈ ((Finset.range power).finsuppAntidiag order).filter
      (fun tuple : Nat →₀ Nat => ∏ index ∈ Finset.range power,
        PowerSeries.coeff (tuple index) series ≠ 0),
    leading ^ (power - (Finset.range power).card) *
      eta ^ (etaPower - ∑ index ∈ Finset.range power,
        henselDenominatorExponent (parts index)) *
        ∏ index ∈ Finset.range power, cleared (parts index)

theorem map_regularClearedSupportedPowerCoefficient_of_specialization
    {O F S : Type*} [CommRing O] [CommRing F] [CommRing S] [DecidableEq S]
    (mapToField : O →+* F) (leading eta : O) (cleared : Nat → O)
    (supportSeries : PowerSeries S) (series : PowerSeries F)
    (power order etaPower : Nat)
    (clearedImage : ∀ parts ∈
        ((Finset.range power).finsuppAntidiag order).filter
          (fun tuple : Nat →₀ Nat => ∏ index ∈ Finset.range power,
            PowerSeries.coeff (tuple index) supportSeries ≠ 0),
      ∀ index ∈ Finset.range power,
      mapToField (cleared (parts index)) =
        mapToField leading *
          mapToField eta ^ henselDenominatorExponent (parts index) *
            PowerSeries.coeff (parts index) series)
    (targetNonzeroImpliesSourceNonzero : ∀ parts ∈
        (Finset.range power).finsuppAntidiag order,
      (∏ index ∈ Finset.range power,
        PowerSeries.coeff (parts index) series) ≠ 0 →
      (∏ index ∈ Finset.range power,
        PowerSeries.coeff (parts index) supportSeries) ≠ 0)
    (exponentBound : ∀ parts ∈
        ((Finset.range power).finsuppAntidiag order).filter
          (fun tuple : Nat →₀ Nat => ∏ index ∈ Finset.range power,
            PowerSeries.coeff (tuple index) supportSeries ≠ 0),
      ∑ index ∈ Finset.range power,
          henselDenominatorExponent (parts index) ≤ etaPower) :
    mapToField (regularClearedSupportedPowerCoefficient leading eta cleared
        supportSeries power order etaPower) =
      mapToField leading ^ power * mapToField eta ^ etaPower *
        PowerSeries.coeff order (series ^ power) := by
  classical
  let tuples := (Finset.range power).finsuppAntidiag order
  let supported := tuples.filter fun tuple : Nat →₀ Nat =>
    ∏ index ∈ Finset.range power,
      PowerSeries.coeff (tuple index) supportSeries ≠ 0
  have supportedSum :
      (∑ parts ∈ supported,
          ∏ index ∈ Finset.range power,
            PowerSeries.coeff (parts index) series) =
        ∑ parts ∈ tuples,
          ∏ index ∈ Finset.range power,
            PowerSeries.coeff (parts index) series := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro parts partsMem partsNotMem
    have productZero :
        ∏ index ∈ Finset.range power,
          PowerSeries.coeff (parts index) series = 0 := by
      by_contra targetProductNeZero
      exact partsNotMem (Finset.mem_filter.mpr
        ⟨partsMem,
          targetNonzeroImpliesSourceNonzero parts partsMem
            targetProductNeZero⟩)
    exact productZero
  unfold regularClearedSupportedPowerCoefficient
  change mapToField
      (∑ parts ∈ supported,
        leading ^ (power - (Finset.range power).card) *
          eta ^ (etaPower - ∑ index ∈ Finset.range power,
            henselDenominatorExponent (parts index)) *
            ∏ index ∈ Finset.range power, cleared (parts index)) = _
  rw [map_sum, PowerSeries.coeff_pow, ← supportedSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro parts partsMem
  simp only [map_mul, map_pow, map_prod]
  have cardLe : (Finset.range power).card ≤ power := by simp
  have clearedProduct :
      ∏ index ∈ Finset.range power, mapToField (cleared (parts index)) =
        ∏ index ∈ Finset.range power,
          (mapToField leading *
            mapToField eta ^ henselDenominatorExponent (parts index)) *
              PowerSeries.coeff (parts index) series := by
    apply Finset.prod_congr rfl
    intro index indexMem
    exact clearedImage parts partsMem index indexMem
  rw [clearedProduct]
  have clearedIdentity := clear_hensel_product_denominators
    (Finset.range power) (mapToField leading) (mapToField eta)
    (fun index => henselDenominatorExponent (parts index))
    (fun index => PowerSeries.coeff (parts index) series)
    power etaPower cardLe (exponentBound parts partsMem)
  simpa only [Finset.card_range] using clearedIdentity.symm

/-- Identity-specialization wrapper. -/
theorem map_regularClearedSupportedPowerCoefficient
    {O F : Type*} [CommRing O] [CommRing F] [DecidableEq F]
    (mapToField : O →+* F) (leading eta : O) (cleared : Nat → O)
    (series : PowerSeries F) (power order etaPower : Nat)
    (clearedImage : ∀ parts ∈
        ((Finset.range power).finsuppAntidiag order).filter
          (fun tuple : Nat →₀ Nat => ∏ index ∈ Finset.range power,
            PowerSeries.coeff (tuple index) series ≠ 0),
      ∀ index ∈ Finset.range power,
      mapToField (cleared (parts index)) =
        mapToField leading *
          mapToField eta ^ henselDenominatorExponent (parts index) *
            PowerSeries.coeff (parts index) series)
    (exponentBound : ∀ parts ∈
        ((Finset.range power).finsuppAntidiag order).filter
          (fun tuple : Nat →₀ Nat => ∏ index ∈ Finset.range power,
            PowerSeries.coeff (tuple index) series ≠ 0),
      ∑ index ∈ Finset.range power,
          henselDenominatorExponent (parts index) ≤ etaPower) :
    mapToField (regularClearedSupportedPowerCoefficient leading eta cleared
        series power order etaPower) =
      mapToField leading ^ power * mapToField eta ^ etaPower *
        PowerSeries.coeff order (series ^ power) := by
  exact map_regularClearedSupportedPowerCoefficient_of_specialization
    mapToField leading eta cleared series series power order etaPower
      clearedImage (fun _ _ nonzero => nonzero) exponentBound

/-! ## Base case of the honest `W * eta^e_t` clearing -/

/-- At order zero the cleared coefficient is the literal integral generator
`T`; no choice or division is involved. -/
def regularClearedHenselCoefficientZero
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K) :
    IntegralLocalBranch localFactor :=
  AdjoinRoot.root (integralLocalFactor localFactor)

theorem integralBranchToFunctionField_regularClearedHenselCoefficientZero
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (root : PowerSeries (LocalBranchField localFactor))
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (eta : IntegralLocalBranch localFactor) :
    integralBranchToFunctionField localFactor
        (regularClearedHenselCoefficientZero localFactor) =
      regularCoefficientMap localFactor localFactor.leadingCoeff *
        integralBranchToFunctionField localFactor eta ^
          AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics.henselDenominatorExponent 0 *
        PowerSeries.coeff 0 root := by
  rw [AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics.henselDenominatorExponent_zero,
    pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff, rootConstant]
  exact (leading_mul_constantBranchRoot localFactor).symm

theorem regularClearedHenselCoefficientZero_weight_le
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (regularClearedHenselCoefficientZero localFactor) ≤
      localBound + ell - ell * localFactor.natDegree := by
  exact integralBranchIteratedWeight_root_le localFactor localFactorNeZero
    ell localBound localCoefficientBound

/-- A convolution product of already-cleared coefficients pays one generator
ceiling per factor and the exact sum of the `eta` exponents. -/
theorem regularClearedCoefficientProduct_weight_le
    {K ι : Type*} [Field K]
    (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound etaWeight : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (indices : Finset ι) (denominatorExponent : ι → Nat)
    (cleared : ι → IntegralLocalBranch localFactor)
    (clearedWeight : ∀ index ∈ indices,
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) (cleared index) ≤
        (localBound + ell - ell * localFactor.natDegree) +
          denominatorExponent index * etaWeight) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (∏ index ∈ indices, cleared index) ≤
      indices.card * (localBound + ell - ell * localFactor.natDegree) +
        (∑ index ∈ indices, denominatorExponent index) * etaWeight := by
  calc
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (∏ index ∈ indices, cleared index) ≤
      ∑ index ∈ indices,
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) (cleared index) :=
      integralBranchIteratedWeight_finset_prod_le localFactor
        localFactorNeZero ell localBound localCoefficientBound indices cleared
    _ ≤ ∑ index ∈ indices,
        ((localBound + ell - ell * localFactor.natDegree) +
          denominatorExponent index * etaWeight) := by
      exact Finset.sum_le_sum fun index indexMem =>
        clearedWeight index indexMem
    _ = indices.card *
          (localBound + ell - ell * localFactor.natDegree) +
        (∑ index ∈ indices, denominatorExponent index) *
          etaWeight := by
      rw [Finset.sum_add_distrib,
        Finset.sum_const_nat (fun _ _ => rfl),
        Finset.sum_mul]

/-- The full cleared convolution coefficient has exactly one generator
ceiling per root factor and the requested total `eta` budget. -/
theorem regularClearedPowerCoefficient_weight_le
    {K : Type*} [Field K]
    (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound etaWeight : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (leading eta : IntegralLocalBranch localFactor)
    (cleared : Nat → IntegralLocalBranch localFactor)
    (power order etaPower : Nat)
    (etaWeightBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) eta ≤ etaWeight)
    (clearedWeight : ∀ parts ∈
        (Finset.range power).finsuppAntidiag order,
      ∀ index ∈ Finset.range power,
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree)
          (cleared (parts index)) ≤
        (localBound + ell - ell * localFactor.natDegree) +
          henselDenominatorExponent (parts index) * etaWeight)
    (exponentBound : ∀ parts ∈
        (Finset.range power).finsuppAntidiag order,
      ∑ index ∈ Finset.range power,
          henselDenominatorExponent (parts index) ≤ etaPower) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (regularClearedPowerCoefficient leading eta cleared
          power order etaPower) ≤
      power * (localBound + ell - ell * localFactor.natDegree) +
        etaPower * etaWeight := by
  classical
  unfold regularClearedPowerCoefficient
  simp only [Finset.card_range, Nat.sub_self, pow_zero, one_mul]
  apply integralBranchIteratedWeight_finset_sum_le localFactor
    localFactorNeZero (localBound + ell - ell * localFactor.natDegree)
      (power * (localBound + ell - ell * localFactor.natDegree) +
        etaPower * etaWeight)
  intro parts partsMem
  let exponentSum := ∑ index ∈ Finset.range power,
    henselDenominatorExponent (parts index)
  have sumLe : exponentSum ≤ etaPower := exponentBound parts partsMem
  have etaPowerSplit : etaPower - exponentSum + exponentSum = etaPower :=
    Nat.sub_add_cancel sumLe
  have etaPowerWeight :
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree)
          (eta ^ (etaPower - exponentSum)) ≤
        (etaPower - exponentSum) * etaWeight := by
    exact (integralBranchIteratedWeight_pow_le localFactor localFactorNeZero
      ell localBound localCoefficientBound eta
        (etaPower - exponentSum)).trans
      (Nat.mul_le_mul_left _ etaWeightBound)
  have productWeight := regularClearedCoefficientProduct_weight_le
    localFactor localFactorNeZero ell localBound etaWeight
      localCoefficientBound (Finset.range power)
      (fun index => henselDenominatorExponent (parts index))
      (fun index => cleared (parts index))
      (fun index indexMem => clearedWeight parts partsMem index indexMem)
  rw [Finset.card_range] at productWeight
  have multiplied := (integralBranchIteratedWeight_mul_le localFactor
    localFactorNeZero ell localBound localCoefficientBound
      (eta ^ (etaPower - exponentSum))
      (∏ index ∈ Finset.range power, cleared (parts index))).trans
        (Nat.add_le_add etaPowerWeight productWeight)
  change integralBranchIteratedWeight localFactor localFactorNeZero
      (localBound + ell - ell * localFactor.natDegree)
      (eta ^ (etaPower - exponentSum) *
        ∏ index ∈ Finset.range power, cleared (parts index)) ≤ _
  refine multiplied.trans ?_
  change (etaPower - exponentSum) * etaWeight +
      (power * (localBound + ell - ell * localFactor.natDegree) +
        exponentSum * etaWeight) ≤ _
  calc
    (etaPower - exponentSum) * etaWeight +
          (power * (localBound + ell - ell * localFactor.natDegree) +
            exponentSum * etaWeight) =
        power * (localBound + ell - ell * localFactor.natDegree) +
          ((etaPower - exponentSum) * etaWeight +
            exponentSum * etaWeight) := by ac_rfl
    _ = power * (localBound + ell - ell * localFactor.natDegree) +
          (etaPower - exponentSum + exponentSum) * etaWeight := by
      rw [Nat.add_mul]
    _ ≤ power * (localBound + ell - ell * localFactor.natDegree) +
          etaPower * etaWeight := by rw [etaPowerSplit]

/-- The same weight estimate restricted to the nonzero convolution support.
This is what makes the nonlinear two-positive-part saving usable without
asserting a false bound for summands that are already zero. -/
theorem regularClearedSupportedPowerCoefficient_weight_le
    {K F : Type*} [Field K] [CommRing F] [DecidableEq F]
    (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound etaWeight : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (leading eta : IntegralLocalBranch localFactor)
    (cleared : Nat → IntegralLocalBranch localFactor)
    (series : PowerSeries F) (power order etaPower : Nat)
    (etaWeightBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) eta ≤ etaWeight)
    (clearedWeight : ∀ parts ∈
        ((Finset.range power).finsuppAntidiag order).filter
          (fun tuple : Nat →₀ Nat => ∏ index ∈ Finset.range power,
            PowerSeries.coeff (tuple index) series ≠ 0),
      ∀ index ∈ Finset.range power,
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree)
          (cleared (parts index)) ≤
        (localBound + ell - ell * localFactor.natDegree) +
          henselDenominatorExponent (parts index) * etaWeight)
    (exponentBound : ∀ parts ∈
        ((Finset.range power).finsuppAntidiag order).filter
          (fun tuple : Nat →₀ Nat => ∏ index ∈ Finset.range power,
            PowerSeries.coeff (tuple index) series ≠ 0),
      ∑ index ∈ Finset.range power,
          henselDenominatorExponent (parts index) ≤ etaPower) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (regularClearedSupportedPowerCoefficient leading eta cleared series
          power order etaPower) ≤
      power * (localBound + ell - ell * localFactor.natDegree) +
        etaPower * etaWeight := by
  classical
  unfold regularClearedSupportedPowerCoefficient
  simp only [Finset.card_range, Nat.sub_self, pow_zero, one_mul]
  apply integralBranchIteratedWeight_finset_sum_le localFactor
    localFactorNeZero (localBound + ell - ell * localFactor.natDegree)
      (power * (localBound + ell - ell * localFactor.natDegree) +
        etaPower * etaWeight)
  intro parts partsMem
  let exponentSum := ∑ index ∈ Finset.range power,
    henselDenominatorExponent (parts index)
  have sumLe : exponentSum ≤ etaPower := exponentBound parts partsMem
  have etaPowerSplit : etaPower - exponentSum + exponentSum = etaPower :=
    Nat.sub_add_cancel sumLe
  have etaPowerWeight :
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree)
          (eta ^ (etaPower - exponentSum)) ≤
        (etaPower - exponentSum) * etaWeight := by
    exact (integralBranchIteratedWeight_pow_le localFactor localFactorNeZero
      ell localBound localCoefficientBound eta
        (etaPower - exponentSum)).trans
      (Nat.mul_le_mul_left _ etaWeightBound)
  have productWeight := regularClearedCoefficientProduct_weight_le
    localFactor localFactorNeZero ell localBound etaWeight
      localCoefficientBound (Finset.range power)
      (fun index => henselDenominatorExponent (parts index))
      (fun index => cleared (parts index))
      (fun index indexMem => clearedWeight parts partsMem index indexMem)
  rw [Finset.card_range] at productWeight
  refine ((integralBranchIteratedWeight_mul_le localFactor
    localFactorNeZero ell localBound localCoefficientBound
      (eta ^ (etaPower - exponentSum))
      (∏ index ∈ Finset.range power, cleared (parts index))).trans
        (Nat.add_le_add etaPowerWeight productWeight)).trans ?_
  change (etaPower - exponentSum) * etaWeight +
      (power * (localBound + ell - ell * localFactor.natDegree) +
        exponentSum * etaWeight) ≤ _
  calc
    (etaPower - exponentSum) * etaWeight +
          (power * (localBound + ell - ell * localFactor.natDegree) +
            exponentSum * etaWeight) =
        power * (localBound + ell - ell * localFactor.natDegree) +
          ((etaPower - exponentSum) * etaWeight +
            exponentSum * etaWeight) := by ac_rfl
    _ = power * (localBound + ell - ell * localFactor.natDegree) +
          (etaPower - exponentSum + exponentSum) * etaWeight := by
      rw [Nat.add_mul]
    _ ≤ power * (localBound + ell - ell * localFactor.natDegree) +
          etaPower * etaWeight := by rw [etaPowerSplit]

/-! ## The nonsaturation issue in the printed Appendix A argument -/

/-- A monic linear branch whose constant term has larger challenge degree.
It satisfies every relevant irreducibility requirement but its leading
coefficient does not saturate the branch weighted-degree ceiling. -/
def nonsaturatedLinearBranch : BivariatePolynomial QM31Exact :=
  X + C (X ^ 2)

theorem nonsaturatedLinearBranch_monic :
    nonsaturatedLinearBranch.Monic := by
  exact Polynomial.monic_X_add_C (X ^ 2)

theorem nonsaturatedLinearBranch_irreducible :
    Irreducible nonsaturatedLinearBranch := by
  apply Polynomial.Monic.irreducible_of_degree_eq_one
    (p := nonsaturatedLinearBranch)
  · exact Polynomial.degree_X_add_C (X ^ 2)
  · exact nonsaturatedLinearBranch_monic

theorem nonsaturatedLinearBranch_iteratedWeight :
    iteratedBivariateWeight 1 nonsaturatedLinearBranch = 2 := by
  apply le_antisymm
  · apply iteratedBivariateWeight_le_of_coeff 1 2
    intro exponent exponentMem
    have exponentLe : exponent ≤ 1 := by
      have exponentLe' :=
        Polynomial.le_natDegree_of_mem_supp exponent exponentMem
      rw [show nonsaturatedLinearBranch = X + C (X ^ 2) by rfl,
        Polynomial.natDegree_X_add_C] at exponentLe'
      exact exponentLe'
    interval_cases exponent
    · rw [show nonsaturatedLinearBranch = X + C (X ^ 2) by rfl,
        Polynomial.coeff_add, Polynomial.coeff_X_zero,
        Polynomial.coeff_C_zero, zero_add]
      simp
    · rw [show nonsaturatedLinearBranch = X + C (X ^ 2) by rfl,
        Polynomial.coeff_add, Polynomial.coeff_X_one,
        Polynomial.coeff_C_of_ne_zero one_ne_zero, add_zero]
      simp
  · have constantMem : 0 ∈ nonsaturatedLinearBranch.support := by
      rw [Polynomial.mem_support_iff]
      rw [show nonsaturatedLinearBranch = X + C (X ^ 2) by rfl,
        Polynomial.coeff_add, Polynomial.coeff_X_zero,
        Polynomial.coeff_C_zero, zero_add]
      exact pow_ne_zero 2 Polynomial.X_ne_zero
    have lower := coeff_weight_le_iteratedBivariateWeight 1
      nonsaturatedLinearBranch 0 constantMem
    rw [show nonsaturatedLinearBranch = X + C (X ^ 2) by rfl,
      Polynomial.coeff_add, Polynomial.coeff_X_zero,
      Polynomial.coeff_C_zero, zero_add] at lower
    simpa only [nonsaturatedLinearBranch, Polynomial.natDegree_X_pow,
      zero_mul, add_zero] using lower

/-- Concrete kernel-checked witness that the source's informal identity
`weight(T) = deg(W) + ell` is not implied by irreducibility and the stated
weighted-degree ceiling.  Here the two sides are `2` and `1`. -/
theorem nonsaturatedLinearBranch_generator_ceiling_ne_leading_add_one :
    localBivariateWeight 1 nonsaturatedLinearBranch + 1 -
          nonsaturatedLinearBranch.natDegree ≠
      nonsaturatedLinearBranch.leadingCoeff.natDegree + 1 := by
  rw [localBivariateWeight_eq_iteratedBivariateWeight]
  rw [nonsaturatedLinearBranch_iteratedWeight]
  rw [show nonsaturatedLinearBranch = X + C (X ^ 2) by rfl,
    Polynomial.natDegree_X_add_C]
  rw [(Polynomial.monic_X_add_C
    (X ^ 2 : Polynomial QM31Exact)).leadingCoeff]
  norm_num

#print axioms derivative_coefficientWeight_le
#print axioms integralBranchIteratedWeight_regularizedHenselDerivative_le
#print axioms leading_mul_constantBranchRoot
#print axioms shiftedXCoefficientHom_eq_coe_taylor
#print axioms coeff_shiftedXCoefficientHom
#print axioms coeff_shiftedChallengeCoefficient
#print axioms shiftedChallengeCoefficient_natDegree_le
#print axioms shiftedChallengeCoefficient_weight_le
#print axioms integralBranchIteratedWeight_shiftedCoefficient_le
#print axioms coeff_localCoefficientPowerSeriesHom
#print axioms coeff_liftedGlobalFactor_coefficient
#print axioms map_regularClearedPowerCoefficient
#print axioms map_regularClearedSupportedPowerCoefficient
#print axioms map_regularClearedSupportedPowerCoefficient_of_specialization
#print axioms integralBranchToFunctionField_regularClearedHenselCoefficientZero
#print axioms regularClearedHenselCoefficientZero_weight_le
#print axioms regularClearedCoefficientProduct_weight_le
#print axioms regularClearedPowerCoefficient_weight_le
#print axioms regularClearedSupportedPowerCoefficient_weight_le
#print axioms nonsaturatedLinearBranch_irreducible
#print axioms nonsaturatedLinearBranch_generator_ceiling_ne_leading_add_one

end

end AspisK1.V7ExactCorrelatedAgreementHenselWeights
