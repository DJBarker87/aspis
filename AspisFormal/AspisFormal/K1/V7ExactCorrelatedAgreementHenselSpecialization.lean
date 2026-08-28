import AspisFormal.K1.V7ExactCorrelatedAgreementHenselIntegralLift
import AspisFormal.K1.V7ExactCorrelatedAgreementRegularZeroCount

/-!
# Specializing the fixed Hensel branch at a concrete challenge

This file proves the denominator-free commuting square needed after the
fixed irreducible local branch has been selected.  A candidate may depend on
the challenge.  At each challenge, its shifted polynomial is compared with
the one global Hensel branch only under the explicit local-factor root and
simple-root hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace AspisK1.V7ExactCorrelatedAgreementHenselSpecialization

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementHensel
open AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics
open AspisK1.V7ExactCorrelatedAgreementHenselWeights
open AspisK1.V7ExactCorrelatedAgreementHenselIntegralLift
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementRegularEvaluation
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementRegularZeroCount
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Substitute `X = x₀ + T` into a base-field polynomial. -/
def shiftedEvaluationHom
    {K : Type*} [Field K] (x₀ : K) : K[X] →+* PowerSeries K :=
  Polynomial.eval₂RingHom PowerSeries.C
    (PowerSeries.C x₀ + PowerSeries.X)

/-- First specialize the challenge `Z=z`, then shift `X=x₀+T`. -/
def specializedShiftedCoefficientHom
    {K : Type*} [Field K] (x₀ z : K) :
    BivariatePolynomial K →+* PowerSeries K :=
  Polynomial.eval₂RingHom (shiftedEvaluationHom x₀) (PowerSeries.C z)

/-- The fixed global factor after concrete challenge specialization and the
literal shifted-`X` substitution. -/
def specializedLiftedGlobalFactor
    {K : Type*} [Field K] (globalFactor : TrivariatePolynomial K)
    (x₀ z : K) : Polynomial (PowerSeries K) :=
  globalFactor.map (specializedShiftedCoefficientHom x₀ z)

/-- The selected challenge-dependent polynomial in shifted power-series
coordinates. -/
def shiftedCandidateSeries
    {K : Type*} [Field K] (x₀ : K) (candidate : K[X]) : PowerSeries K :=
  shiftedEvaluationHom x₀ candidate

theorem specializedShiftedCoefficientHom_eq_comp
    {K : Type*} [Field K] (x₀ z : K) :
    specializedShiftedCoefficientHom x₀ z =
      (shiftedEvaluationHom x₀).comp
        (Polynomial.evalRingHom (C z)) := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    simp [specializedShiftedCoefficientHom, shiftedEvaluationHom]
  · simp [specializedShiftedCoefficientHom, shiftedEvaluationHom]

theorem shiftedEvaluationHom_eq_coe_taylor
    {K : Type*} [Field K] (x₀ : K) (polynomial : K[X]) :
    shiftedEvaluationHom x₀ polynomial =
      (Polynomial.taylor x₀ polynomial : PowerSeries K) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      rw [map_add, leftInduction, rightInduction, map_add]
      exact (Polynomial.coe_add (Polynomial.taylor x₀ left)
        (Polynomial.taylor x₀ right)).symm
  | monomial exponent coefficient =>
      change Polynomial.eval₂ PowerSeries.C
          (PowerSeries.C x₀ + PowerSeries.X)
          (Polynomial.monomial exponent coefficient) = _
      rw [Polynomial.eval₂_monomial, Polynomial.taylor_monomial,
        Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
        Polynomial.coe_add, Polynomial.coe_X]
      rw [add_comm]
      rw [Polynomial.coe_C]

theorem coeff_shiftedEvaluationHom
    {K : Type*} [Field K] (x₀ : K) (polynomial : K[X]) (order : Nat) :
    PowerSeries.coeff order (shiftedEvaluationHom x₀ polynomial) =
      (Polynomial.hasseDeriv order polynomial).eval x₀ := by
  rw [shiftedEvaluationHom_eq_coe_taylor, Polynomial.coeff_coe,
    Polynomial.taylor_coeff]

/-- Exact coefficient commuting square for the regular representative of a
shifted trivariate coefficient. -/
theorem coeff_specializedShiftedCoefficientHom
    {K : Type*} [Field K] (x₀ z : K)
    (polynomial : BivariatePolynomial K) (order : Nat) :
    PowerSeries.coeff order
        (specializedShiftedCoefficientHom x₀ z polynomial) =
      (shiftedChallengeCoefficient x₀ order polynomial).eval z := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      rw [map_add, map_add, shiftedChallengeCoefficient_add,
        Polynomial.eval_add, leftInduction, rightInduction]
  | monomial challengeExponent coefficient =>
      rw [specializedShiftedCoefficientHom_eq_comp, RingHom.comp_apply,
        coe_evalRingHom, Polynomial.eval_monomial, map_mul, map_pow]
      change PowerSeries.coeff order
        (shiftedEvaluationHom x₀ coefficient *
          shiftedEvaluationHom x₀ (C z) ^ challengeExponent) = _
      rw [show shiftedEvaluationHom x₀ (C z) ^ challengeExponent =
          PowerSeries.C (z ^ challengeExponent) by
        simp [shiftedEvaluationHom]]
      rw [PowerSeries.coeff_mul_C]
      rw [shiftedChallengeCoefficient_monomial, eval_monomial]
      change PowerSeries.coeff order (shiftedEvaluationHom x₀ coefficient) *
          z ^ challengeExponent =
        (Polynomial.hasseDeriv order coefficient).eval x₀ *
          z ^ challengeExponent
      rw [coeff_shiftedEvaluationHom]

theorem integralBranchSpecialization_regularLiftedGlobalCoefficient
    (globalFactor : TrivariatePolynomial QM31Exact)
    (x₀ z y : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    (localFactorPositive : 0 < localFactor.natDegree)
    (localRoot : localFactor.eval₂ (Polynomial.evalRingHom z) y = 0)
    (yExponent order : Nat) :
    integralBranchSpecialization localFactor z
        (localFactor.leadingCoeff.eval z * y)
        (integralLocalFactor_root_of_localFactor_root localFactor
          localFactorPositive z y localRoot)
        (regularLiftedGlobalCoefficient globalFactor x₀ localFactor
          yExponent order) =
      PowerSeries.coeff order
        ((specializedLiftedGlobalFactor globalFactor x₀ z).coeff
          yExponent) := by
  rw [regularLiftedGlobalCoefficient,
    integralBranchSpecialization_of,
    specializedLiftedGlobalFactor, Polynomial.coeff_map,
    coeff_specializedShiftedCoefficientHom]

theorem specializedLiftedGlobalFactor_eq_map_specializeChallenge
    {K : Type*} [Field K] (globalFactor : TrivariatePolynomial K)
    (x₀ z : K) :
    specializedLiftedGlobalFactor globalFactor x₀ z =
      (specializeChallenge z globalFactor).map (shiftedEvaluationHom x₀) := by
  unfold specializedLiftedGlobalFactor specializeChallenge
  rw [specializedShiftedCoefficientHom_eq_comp, ← Polynomial.map_map]
  rfl

/-- A challenge-dependent candidate which is an ordinary specialized factor
root remains a root after the literal shifted-`X` embedding. -/
theorem shiftedCandidateSeries_isRoot
    {K : Type*} [Field K] (globalFactor : TrivariatePolynomial K)
    (x₀ z : K) (candidate : K[X])
    (candidateRoot : challengeCandidateHom z candidate globalFactor = 0) :
    (specializedLiftedGlobalFactor globalFactor x₀ z).IsRoot
      (shiftedCandidateSeries x₀ candidate) := by
  rw [Polynomial.IsRoot,
    specializedLiftedGlobalFactor_eq_map_specializeChallenge]
  change ((specializeChallenge z globalFactor).map
      (shiftedEvaluationHom x₀)).eval
        (shiftedEvaluationHom x₀ candidate) = 0
  rw [Polynomial.eval_map]
  calc
    Polynomial.eval₂ (shiftedEvaluationHom x₀)
        (shiftedEvaluationHom x₀ candidate)
        (specializeChallenge z globalFactor) =
      shiftedEvaluationHom x₀
        ((specializeChallenge z globalFactor).eval candidate) := by
      symm
      simpa using Polynomial.hom_eval₂
        (specializeChallenge z globalFactor) (RingHom.id (Polynomial K))
          (shiftedEvaluationHom x₀) candidate
    _ = 0 := by
      change shiftedEvaluationHom x₀
          (challengeCandidateHom z candidate globalFactor) = 0
      rw [candidateRoot, map_zero]

@[simp] theorem constantCoeff_shiftedCandidateSeries
    {K : Type*} [Field K] (x₀ : K) (candidate : K[X]) :
    PowerSeries.constantCoeff (shiftedCandidateSeries x₀ candidate) =
      candidate.eval x₀ := by
  unfold shiftedCandidateSeries
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [coeff_shiftedEvaluationHom]
  simp

theorem constantCoeff_comp_specializedShiftedCoefficientHom
    {K : Type*} [Field K] (x₀ z : K) :
    (PowerSeries.constantCoeff (R := K)).comp
        (specializedShiftedCoefficientHom x₀ z) =
      (Polynomial.evalRingHom z).comp (evaluateInnerVariable x₀) := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    simp [specializedShiftedCoefficientHom, evaluateInnerVariable]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_shiftedEvaluationHom]
    simp
  · simp [specializedShiftedCoefficientHom, shiftedEvaluationHom,
      evaluateInnerVariable]

theorem constantCoeff_specializedLiftedGlobalFactor_eval_C
    {K : Type*} [Field K] (globalFactor : TrivariatePolynomial K)
    (x₀ z candidate : K) :
    PowerSeries.constantCoeff
        ((specializedLiftedGlobalFactor globalFactor x₀ z).eval
          (PowerSeries.C candidate)) =
      (((specializeEvaluationPoint x₀ globalFactor).map
        (Polynomial.evalRingHom z))).eval candidate := by
  unfold specializedLiftedGlobalFactor
  rw [Polynomial.eval_map, Polynomial.hom_eval₂]
  rw [constantCoeff_comp_specializedShiftedCoefficientHom]
  simp only [PowerSeries.constantCoeff_C]
  rw [Polynomial.eval_map]
  exact (Polynomial.eval₂_map (evaluateInnerVariable x₀)
    (Polynomial.evalRingHom z) candidate).symm

theorem constantCoeff_specializedLiftedGlobalFactor_derivative_eval_C
    {K : Type*} [Field K] (globalFactor : TrivariatePolynomial K)
    (x₀ z candidate : K) :
    PowerSeries.constantCoeff
        ((specializedLiftedGlobalFactor globalFactor x₀ z).derivative.eval
          (PowerSeries.C candidate)) =
      ((((specializeEvaluationPoint x₀ globalFactor).derivative).map
        (Polynomial.evalRingHom z))).eval candidate := by
  have specializedDerivative :
      specializeEvaluationPoint x₀ globalFactor.derivative =
        (specializeEvaluationPoint x₀ globalFactor).derivative := by
    change globalFactor.derivative.map (evaluateInnerVariable x₀) =
      (globalFactor.map (evaluateInnerVariable x₀)).derivative
    rw [Polynomial.derivative_map]
  calc
    PowerSeries.constantCoeff
        ((specializedLiftedGlobalFactor globalFactor x₀ z).derivative.eval
          (PowerSeries.C candidate)) =
        PowerSeries.constantCoeff
          ((specializedLiftedGlobalFactor globalFactor.derivative x₀ z).eval
            (PowerSeries.C candidate)) := by
      simp only [specializedLiftedGlobalFactor, Polynomial.derivative_map]
    _ = (((specializeEvaluationPoint x₀ globalFactor.derivative).map
          (Polynomial.evalRingHom z))).eval candidate :=
      constantCoeff_specializedLiftedGlobalFactor_eval_C
        globalFactor.derivative x₀ z candidate
    _ = _ := by rw [specializedDerivative]

/-! ## One concrete cleared lift, shared by every specialization -/

/-- Choose once, in the fixed integral branch, the denominator-cleared
coefficient supplied by the kernel-proved Hensel recurrence.  This choice is
made before and independently of every concrete challenge. -/
noncomputable def chosenRegularClearedHenselCoefficient
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (order : Nat) : IntegralLocalBranch localFactor :=
  Classical.choose (exists_regularClearedHenselCoefficient globalFactor
    globalFactorPositive x₀ localFactor root rootEquation rootConstant order)

theorem chosenRegularClearedHenselCoefficient_image
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (order : Nat) :
    integralBranchToFunctionField localFactor
        (chosenRegularClearedHenselCoefficient globalFactor
          globalFactorPositive x₀ localFactor root rootEquation rootConstant
          order) =
      regularCoefficientMap localFactor localFactor.leadingCoeff *
        integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent order * PowerSeries.coeff order root :=
  Classical.choose_spec (exists_regularClearedHenselCoefficient globalFactor
    globalFactorPositive x₀ localFactor root rootEquation rootConstant order)

/-- The once-chosen cleared coefficient inherits the constructive weight
bound.  The weighted existence theorem and the fixed choice have the same
faithful function-field image, so they are equal in the integral branch. -/
theorem chosenRegularClearedHenselCoefficient_weight_le
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
    (order : Nat) :
    let etaWeight := (parentBound - ell) +
      (globalFactor.natDegree - 1) *
        (localBound - ell * localFactor.natDegree)
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (chosenRegularClearedHenselCoefficient globalFactor
          globalFactorPositive x₀ localFactor root rootEquation rootConstant
          order) ≤
      (localBound + ell - ell * localFactor.natDegree) +
        henselDenominatorExponent order * etaWeight := by
  dsimp only
  obtain ⟨weighted, weightedImage, weightedBound⟩ :=
    exists_regularClearedHenselCoefficient_with_weight globalFactor
      globalFactorPositive x₀ localFactor localFactorNeZero ell localBound
      parentBound ellLeParent localCoefficientBound globalCoefficientBound
      root rootEquation rootConstant order
  have chosenEqWeighted :
      chosenRegularClearedHenselCoefficient globalFactor
          globalFactorPositive x₀ localFactor root rootEquation rootConstant
          order = weighted := by
    apply integralBranchToFunctionField_injective localFactor localFactorNeZero
      localFactorPositive
    rw [chosenRegularClearedHenselCoefficient_image]
    exact weightedImage.symm
  rw [chosenEqWeighted]
  exact weightedBound

theorem chosenRegularClearedHenselCoefficient_zero
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (localFactorPositive : 0 < localFactor.natDegree)
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor)) :
    chosenRegularClearedHenselCoefficient globalFactor globalFactorPositive x₀
        localFactor root rootEquation rootConstant 0 =
      regularClearedHenselCoefficientZero localFactor := by
  apply integralBranchToFunctionField_injective localFactor localFactorNeZero
    localFactorPositive
  rw [chosenRegularClearedHenselCoefficient_image]
  exact integralBranchToFunctionField_regularClearedHenselCoefficientZero
    localFactor root rootConstant
      (regularizedHenselDerivative globalFactor x₀ localFactor) |>.symm

theorem chosenRegularClearedHenselCoefficient_succ
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (localFactorPositive : 0 < localFactor.natDegree)
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (order : Nat) (orderPositive : 0 < order) :
    chosenRegularClearedHenselCoefficient globalFactor globalFactorPositive x₀
        localFactor root rootEquation rootConstant order =
      -regularClearedNonlinearEvaluationCoefficientOn globalFactor.support
        (regularLiftedGlobalCoefficient globalFactor x₀ localFactor) root
        (AdjoinRoot.of (integralLocalFactor localFactor)
          localFactor.leadingCoeff)
        (regularizedHenselDerivative globalFactor x₀ localFactor)
        (chosenRegularClearedHenselCoefficient globalFactor
          globalFactorPositive x₀ localFactor root rootEquation rootConstant)
        globalFactor.natDegree order := by
  apply integralBranchToFunctionField_injective localFactor localFactorNeZero
    localFactorPositive
  rw [chosenRegularClearedHenselCoefficient_image]
  exact (regularClearedHenselNext_image globalFactor globalFactorPositive x₀
    localFactor root rootEquation rootConstant order orderPositive
    (chosenRegularClearedHenselCoefficient globalFactor globalFactorPositive x₀
      localFactor root rootEquation rootConstant)
    (fun lower lowerBound =>
      chosenRegularClearedHenselCoefficient_image globalFactor
        globalFactorPositive x₀ localFactor root rootEquation rootConstant
        lower)).symm

theorem specialization_regularizedHenselDerivative
    (globalFactor : TrivariatePolynomial QM31Exact)
    (x₀ z y : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    (localFactorPositive : 0 < localFactor.natDegree)
    (localRoot : localFactor.eval₂ (Polynomial.evalRingHom z) y = 0) :
    let rootPair := integralLocalFactor_root_of_localFactor_root localFactor
      localFactorPositive z y localRoot
    integralBranchSpecialization localFactor z
        (localFactor.leadingCoeff.eval z * y) rootPair
        (regularizedHenselDerivative globalFactor x₀ localFactor) =
      localFactor.leadingCoeff.eval z ^ (globalFactor.natDegree - 1) *
        PowerSeries.constantCoeff
          ((specializedLiftedGlobalFactor globalFactor x₀ z).derivative.eval
            (PowerSeries.C y)) := by
  dsimp only
  rw [regularizedHenselDerivative]
  rw [integralBranchSpecialization_regularizedBranchEvaluation localFactor
    (specializeEvaluationPoint x₀ globalFactor).derivative
    (globalFactor.natDegree - 1)
    (specializedDerivative_natDegree_le_global_sub_one globalFactor x₀)
    z y localFactorPositive localRoot]
  rw [constantCoeff_specializedLiftedGlobalFactor_derivative_eval_C,
    Polynomial.eval_map]

/-- Every concrete challenge specialization sees the same cleared global
branch coefficient as the correspondingly shifted, challenge-dependent
candidate coefficient.  Candidate selection remains under `∀ z`; the fixed
integral branch and its coefficients do not depend on `z`. -/
theorem specialization_chosenRegularClearedHenselCoefficient
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (localFactorPositive : 0 < localFactor.natDegree)
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (z : QM31Exact) (candidate : QM31Exact[X])
    (localRoot : localFactor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0)
    (candidateRoot : challengeCandidateHom z candidate globalFactor = 0)
    (simple : SimpleSpecializedRoot globalFactor x₀ z candidate)
    (notPole : z ∉ localPoleChallengeSet localFactor)
    (order : Nat) :
    let rootPair := integralLocalFactor_root_of_localFactor_root localFactor
      localFactorPositive z (candidate.eval x₀) localRoot
    let specialization := integralBranchSpecialization localFactor z
      (localFactor.leadingCoeff.eval z * candidate.eval x₀) rootPair
    specialization
        (chosenRegularClearedHenselCoefficient globalFactor
          globalFactorPositive x₀ localFactor root rootEquation rootConstant
          order) =
      specialization
          (AdjoinRoot.of (integralLocalFactor localFactor)
            localFactor.leadingCoeff) *
        specialization
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent order *
            PowerSeries.coeff order
              (shiftedCandidateSeries x₀ candidate) := by
  dsimp only
  let rootPair := integralLocalFactor_root_of_localFactor_root localFactor
    localFactorPositive z (candidate.eval x₀) localRoot
  let specialization := integralBranchSpecialization localFactor z
    (localFactor.leadingCoeff.eval z * candidate.eval x₀) rootPair
  have leadingSpecializationNeZero :
      specialization
          (AdjoinRoot.of (integralLocalFactor localFactor)
            localFactor.leadingCoeff) ≠ 0 := by
    rw [integralBranchSpecialization_of]
    exact fun leadingZero => notPole
      ((mem_localPoleChallengeSet_iff localFactor localFactorNeZero z).mpr
        leadingZero)
  have etaSpecializationNeZero :
      specialization
          (regularizedHenselDerivative globalFactor x₀ localFactor) ≠ 0 :=
    specialization_regularizedHenselDerivative_ne_zero globalFactor x₀ z
      localFactor localFactorNeZero localFactorPositive candidate localRoot
        simple notPole
  induction order using Nat.strong_induction_on with
  | h order induction =>
      by_cases orderZero : order = 0
      · subst order
        rw [chosenRegularClearedHenselCoefficient_zero globalFactor
          globalFactorPositive x₀ localFactor localFactorNeZero
          localFactorPositive root rootEquation rootConstant]
        simp only [regularClearedHenselCoefficientZero, specialization,
          integralBranchSpecialization_root,
          henselDenominatorExponent_zero, pow_zero, mul_one,
          PowerSeries.coeff_zero_eq_constantCoeff,
          constantCoeff_shiftedCandidateSeries]
        rw [integralBranchSpecialization_of]
      · have orderPositive : 0 < order := Nat.pos_of_ne_zero orderZero
        have coefficientImage : ∀ exponent coefficientOrder,
            specialization
                (regularLiftedGlobalCoefficient globalFactor x₀ localFactor
                  exponent coefficientOrder) =
              PowerSeries.coeff coefficientOrder
                ((specializedLiftedGlobalFactor globalFactor x₀ z).coeff
                  exponent) := by
          intro exponent coefficientOrder
          exact integralBranchSpecialization_regularLiftedGlobalCoefficient
            globalFactor x₀ z (candidate.eval x₀) localFactor
              localFactorPositive localRoot exponent coefficientOrder
        have clearedImage : ∀ lower < order,
            specialization
                (chosenRegularClearedHenselCoefficient globalFactor
                  globalFactorPositive x₀ localFactor root rootEquation
                    rootConstant lower) =
              specialization
                  (AdjoinRoot.of (integralLocalFactor localFactor)
                    localFactor.leadingCoeff) *
                specialization
                    (regularizedHenselDerivative globalFactor x₀
                      localFactor) ^ henselDenominatorExponent lower *
                  PowerSeries.coeff lower
                    (shiftedCandidateSeries x₀ candidate) := by
          intro lower lowerBound
          exact induction lower lowerBound
        have candidateSeriesRoot :
            (specializedLiftedGlobalFactor globalFactor x₀ z).IsRoot
              (shiftedCandidateSeries x₀ candidate) :=
          shiftedCandidateSeries_isRoot globalFactor x₀ z candidate
            candidateRoot
        have etaImage : specialization
              (regularizedHenselDerivative globalFactor x₀ localFactor) =
            specialization
                (AdjoinRoot.of (integralLocalFactor localFactor)
                  localFactor.leadingCoeff) ^
              (globalFactor.natDegree - 1) *
                PowerSeries.constantCoeff
                  ((specializedLiftedGlobalFactor globalFactor x₀ z).derivative.eval
                    (PowerSeries.C
                      (PowerSeries.constantCoeff
                        (shiftedCandidateSeries x₀ candidate)))) := by
          rw [specialization_regularizedHenselDerivative globalFactor x₀
            z (candidate.eval x₀) localFactor localFactorPositive localRoot]
          rw [integralBranchSpecialization_of,
            constantCoeff_shiftedCandidateSeries]
        have specializedSupportSubset :
            (specializedLiftedGlobalFactor globalFactor x₀ z).support ⊆
              globalFactor.support := by
          unfold specializedLiftedGlobalFactor
          exact Polynomial.support_map_subset
            (specializedShiftedCoefficientHom x₀ z) globalFactor
        have supportOfTarget : ∀ lower < order,
            PowerSeries.coeff lower (shiftedCandidateSeries x₀ candidate) ≠ 0 →
              PowerSeries.coeff lower root ≠ 0 := by
          intro lower lowerBound targetCoefficientNeZero
          have mappedClearedNeZero :
              specialization
                  (chosenRegularClearedHenselCoefficient globalFactor
                    globalFactorPositive x₀ localFactor root rootEquation
                      rootConstant lower) ≠ 0 := by
            rw [induction lower lowerBound]
            exact mul_ne_zero
              (mul_ne_zero leadingSpecializationNeZero
                (pow_ne_zero _ etaSpecializationNeZero))
              targetCoefficientNeZero
          intro sourceCoefficientZero
          have clearedZero :
              chosenRegularClearedHenselCoefficient globalFactor
                  globalFactorPositive x₀ localFactor root rootEquation
                    rootConstant lower = 0 := by
            apply integralBranchToFunctionField_injective localFactor
              localFactorNeZero localFactorPositive
            rw [chosenRegularClearedHenselCoefficient_image,
              sourceCoefficientZero, mul_zero, map_zero]
          exact mappedClearedNeZero (by rw [clearedZero, map_zero])
        have specializedStep :
            specialization
                (-regularClearedNonlinearEvaluationCoefficientOn
                  globalFactor.support
                  (regularLiftedGlobalCoefficient globalFactor x₀ localFactor)
                  root
                  (AdjoinRoot.of (integralLocalFactor localFactor)
                    localFactor.leadingCoeff)
                  (regularizedHenselDerivative globalFactor x₀ localFactor)
                  (chosenRegularClearedHenselCoefficient globalFactor
                    globalFactorPositive x₀ localFactor root rootEquation
                      rootConstant)
                  globalFactor.natDegree order) =
              specialization
                  (AdjoinRoot.of (integralLocalFactor localFactor)
                    localFactor.leadingCoeff) *
                specialization
                    (regularizedHenselDerivative globalFactor x₀
                      localFactor) ^ henselDenominatorExponent order *
                  PowerSeries.coeff order
                    (shiftedCandidateSeries x₀ candidate) :=
          map_neg_regularClearedNonlinearEvaluationCoefficientOn_of_isRoot
          (O := IntegralLocalBranch localFactor) (F := QM31Exact)
          (S := LocalBranchField localFactor)
          (mapToField := specialization)
          (indices := globalFactor.support)
          (polynomial := specializedLiftedGlobalFactor globalFactor x₀ z)
          (coefficientRepresentative :=
            regularLiftedGlobalCoefficient globalFactor x₀ localFactor)
          (supportSeries := root)
          (series := shiftedCandidateSeries x₀ candidate)
          (leading := AdjoinRoot.of (integralLocalFactor localFactor)
            localFactor.leadingCoeff)
          (eta := regularizedHenselDerivative globalFactor x₀ localFactor)
          (cleared := chosenRegularClearedHenselCoefficient globalFactor
            globalFactorPositive x₀ localFactor root rootEquation
              rootConstant)
          (degree := globalFactor.natDegree) (order := order)
          globalFactorPositive orderPositive
          (fun exponent exponentMem =>
            Polynomial.le_natDegree_of_mem_supp exponent exponentMem)
          specializedSupportSubset coefficientImage clearedImage
          supportOfTarget candidateSeriesRoot etaImage
        rw [chosenRegularClearedHenselCoefficient_succ globalFactor
          globalFactorPositive x₀ localFactor localFactorNeZero
          localFactorPositive root rootEquation rootConstant order
          orderPositive]
        exact specializedStep

theorem coeff_shiftedCandidateSeries_eq_zero_of_natDegree_lt
    (x₀ : QM31Exact) (candidate : QM31Exact[X]) (order : Nat)
    (degreeLt : candidate.natDegree < order) :
    PowerSeries.coeff order (shiftedCandidateSeries x₀ candidate) = 0 := by
  rw [shiftedCandidateSeries, coeff_shiftedEvaluationHom,
    Polynomial.hasseDeriv_eq_zero_of_lt_natDegree candidate order degreeLt,
    Polynomial.eval_zero]

/-- More challenge-dependent simple specializations than the exact
branch-weight budget force a fixed cleared coefficient to vanish.  Each
candidate may be chosen independently at its challenge; the only shared
objects are the already selected irreducible branches and Hensel root. -/
theorem chosenRegularClearedHenselCoefficient_eq_zero_of_many_specializations
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
    (order : Nat)
    (candidateDegreeLt : ∀ z ∈ challenges,
      (candidate z).natDegree < order)
    (tooMany : localFactor.natDegree *
        ((localBound + ell - ell * localFactor.natDegree) +
          henselDenominatorExponent order *
            ((parentBound - ell) + (globalFactor.natDegree - 1) *
              (localBound - ell * localFactor.natDegree))) <
      challenges.card) :
    chosenRegularClearedHenselCoefficient globalFactor globalFactorPositive x₀
        localFactor root rootEquation rootConstant order = 0 := by
  let rootValue : QM31Exact → QM31Exact := fun z =>
    localFactor.leadingCoeff.eval z * (candidate z).eval x₀
  have rootPair : ∀ z ∈ challenges,
      (integralLocalFactor localFactor).eval₂ (Polynomial.evalRingHom z)
        (rootValue z) = 0 := by
    intro z zMem
    exact integralLocalFactor_root_of_localFactor_root localFactor
      localFactorPositive z ((candidate z).eval x₀) (localRoot z zMem)
  have specializationZero : ∀ z (zMem : z ∈ challenges),
      integralBranchSpecialization localFactor z (rootValue z)
          (rootPair z zMem)
          (chosenRegularClearedHenselCoefficient globalFactor
            globalFactorPositive x₀ localFactor root rootEquation rootConstant
            order) = 0 := by
    intro z zMem
    have specialized := specialization_chosenRegularClearedHenselCoefficient
      globalFactor globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive root rootEquation rootConstant z (candidate z)
      (localRoot z zMem) (candidateRoot z zMem) (simple z zMem)
      (notPole z zMem) order
    rw [specialized,
      coeff_shiftedCandidateSeries_eq_zero_of_natDegree_lt x₀ (candidate z)
        order (candidateDegreeLt z zMem), mul_zero]
  apply integralBranch_eq_zero_of_mul_weight_lt_card localFactor
    localFactorNeZero localFactorPositive ell localBound localCoefficientBound
    (chosenRegularClearedHenselCoefficient globalFactor globalFactorPositive x₀
      localFactor root rootEquation rootConstant order)
    challenges rootValue rootPair specializationZero
  exact (Nat.mul_le_mul_left localFactor.natDegree
    (chosenRegularClearedHenselCoefficient_weight_le globalFactor
      globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive ell localBound parentBound ellLeParent
      localCoefficientBound globalCoefficientBound root rootEquation
      rootConstant order)).trans_lt tooMany

/-- Vanishing of a cleared coefficient really kills the corresponding fixed
Hensel coefficient when the explicit derivative denominator is nonzero. -/
theorem coeff_fixedBranchRoot_eq_zero_of_chosenRegularCleared_eq_zero
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (localFactorPositive : 0 < localFactor.natDegree)
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (etaNeZero : regularizedHenselDerivative globalFactor x₀ localFactor ≠ 0)
    (order : Nat)
    (clearedZero :
      chosenRegularClearedHenselCoefficient globalFactor globalFactorPositive x₀
          localFactor root rootEquation rootConstant order = 0) :
    PowerSeries.coeff order root = 0 := by
  have leadingNeZero : localFactor.leadingCoeff ≠ 0 :=
    mt Polynomial.leadingCoeff_eq_zero.mp localFactorNeZero
  have mappedLeadingNeZero :
      regularCoefficientMap localFactor localFactor.leadingCoeff ≠ 0 := by
    intro mappedZero
    exact leadingNeZero (regularCoefficientMap_injective localFactor <| by
      simpa only [map_zero] using mappedZero)
  have mappedEtaNeZero : integralBranchToFunctionField localFactor
      (regularizedHenselDerivative globalFactor x₀ localFactor) ≠ 0 := by
    intro mappedZero
    apply etaNeZero
    apply integralBranchToFunctionField_injective localFactor localFactorNeZero
      localFactorPositive
    simpa only [map_zero] using mappedZero
  have image := chosenRegularClearedHenselCoefficient_image globalFactor
    globalFactorPositive x₀ localFactor root rootEquation rootConstant order
  rw [clearedZero, map_zero] at image
  by_contra coefficientNeZero
  exact (mul_ne_zero
    (mul_ne_zero mappedLeadingNeZero
      (pow_ne_zero _ mappedEtaNeZero)) coefficientNeZero) image.symm

/-- Combined fixed-branch zero extraction: sufficiently many independently
selected, simple, pole-free polynomial roots of degree below `order` force
the order-`order` coefficient of the one global Hensel branch to vanish. -/
theorem coeff_fixedBranchRoot_eq_zero_of_many_specializations
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
    (order : Nat)
    (candidateDegreeLt : ∀ z ∈ challenges,
      (candidate z).natDegree < order)
    (tooMany : localFactor.natDegree *
        ((localBound + ell - ell * localFactor.natDegree) +
          henselDenominatorExponent order *
            ((parentBound - ell) + (globalFactor.natDegree - 1) *
              (localBound - ell * localFactor.natDegree))) <
      challenges.card) :
    PowerSeries.coeff order root = 0 := by
  apply coeff_fixedBranchRoot_eq_zero_of_chosenRegularCleared_eq_zero
    globalFactor globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive root rootEquation rootConstant etaNeZero order
  exact chosenRegularClearedHenselCoefficient_eq_zero_of_many_specializations
    globalFactor globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive ell localBound parentBound ellLeParent
      localCoefficientBound globalCoefficientBound root rootEquation
      rootConstant challenges candidate localRoot candidateRoot simple notPole
      order candidateDegreeLt tooMany

#print axioms chosenRegularClearedHenselCoefficient_image
#print axioms chosenRegularClearedHenselCoefficient_succ
#print axioms specialization_regularizedHenselDerivative
#print axioms specialization_chosenRegularClearedHenselCoefficient
#print axioms chosenRegularClearedHenselCoefficient_weight_le
#print axioms chosenRegularClearedHenselCoefficient_eq_zero_of_many_specializations
#print axioms coeff_fixedBranchRoot_eq_zero_of_chosenRegularCleared_eq_zero
#print axioms coeff_fixedBranchRoot_eq_zero_of_many_specializations

#print axioms specializedShiftedCoefficientHom_eq_comp
#print axioms coeff_specializedShiftedCoefficientHom
#print axioms integralBranchSpecialization_regularLiftedGlobalCoefficient
#print axioms shiftedCandidateSeries_isRoot
#print axioms constantCoeff_specializedLiftedGlobalFactor_derivative_eval_C

end

end AspisK1.V7ExactCorrelatedAgreementHenselSpecialization
