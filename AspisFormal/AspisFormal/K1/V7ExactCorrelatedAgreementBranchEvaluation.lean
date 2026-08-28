import AspisFormal.K1.V7ExactCorrelatedAgreementFiniteBranch
import AspisFormal.K1.V7ExactCorrelatedAgreementIncidence

/-!
# Uniform evaluation of the fixed finite Hensel branch

The individual Hensel coefficients have different derivative denominators.
This file raises all of them to one common exponent before evaluating the
finite Taylor branch.  The result is an element of the fixed integral branch,
so the existing resultant zero count applies.  Its specialization is proved
against each independently selected candidate; no specialization hom from an
algebraic function field is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace AspisK1.V7ExactCorrelatedAgreementBranchEvaluation

open scoped BigOperators
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics
open AspisK1.V7ExactCorrelatedAgreementHenselSpecialization
open AspisK1.V7ExactCorrelatedAgreementHenselWeights
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementRegularZeroCount
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A base-field scalar embedded into the fixed integral local branch. -/
def integralBranchScalar (localFactor : BivariatePolynomial QM31Exact)
    (value : QM31Exact) : IntegralLocalBranch localFactor :=
  AdjoinRoot.of (integralLocalFactor localFactor) (C value)

/-- The denominator-free evaluation of the first `xBound` Taylor
coefficients.  Every summand is cleared to the one common Hensel denominator
exponent `2*(xBound-1)-1`. -/
def clearedFiniteBranchEvaluation
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
    (xBound : Nat) (x : QM31Exact) : IntegralLocalBranch localFactor :=
  ∑ order ∈ Finset.range xBound,
    integralBranchScalar localFactor ((x - x₀) ^ order) *
      regularizedHenselDerivative globalFactor x₀ localFactor ^
        (henselDenominatorExponent (xBound - 1) -
          henselDenominatorExponent order) *
      chosenRegularClearedHenselCoefficient globalFactor
        globalFactorPositive x₀ localFactor root rootEquation rootConstant order

theorem henselDenominatorExponent_le_of_lt
    {order xBound : Nat} (orderLt : order < xBound) :
    henselDenominatorExponent order ≤
      henselDenominatorExponent (xBound - 1) := by
  unfold henselDenominatorExponent
  omega

/-- In the selected algebraic function field, the integral evaluation is
literally the fixed Taylor branch multiplied by one common nonzero clearing
factor. -/
theorem integralBranchToFunctionField_clearedFiniteBranchEvaluation
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
    (xBound : Nat) (x : QM31Exact) :
    integralBranchToFunctionField localFactor
        (clearedFiniteBranchEvaluation globalFactor globalFactorPositive x₀
          localFactor root rootEquation rootConstant xBound x) =
      regularCoefficientMap localFactor localFactor.leadingCoeff *
        integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent (xBound - 1) *
        (∑ order ∈ Finset.range xBound,
          regularCoefficientMap localFactor (C ((x - x₀) ^ order)) *
            PowerSeries.coeff order root) := by
  classical
  unfold clearedFiniteBranchEvaluation integralBranchScalar
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro order orderMem
  have orderLt : order < xBound := Finset.mem_range.mp orderMem
  have exponentLe := henselDenominatorExponent_le_of_lt orderLt
  simp only [map_mul, map_pow]
  rw [integralBranchToFunctionField_of,
    chosenRegularClearedHenselCoefficient_image]
  have powerCombine :
      integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          (henselDenominatorExponent (xBound - 1) -
            henselDenominatorExponent order) *
        integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent order =
        integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent (xBound - 1) := by
    rw [← pow_add, Nat.sub_add_cancel exponentLe]
  rw [← powerCombine]
  ring

/-- At every explicit simple, pole-free specialization, the same integral
element evaluates to the independently selected candidate's Taylor value,
with exactly the same common clearing factor. -/
theorem specialization_clearedFiniteBranchEvaluation
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
    (xBound : Nat) (x : QM31Exact) :
    let rootPair := integralLocalFactor_root_of_localFactor_root localFactor
      localFactorPositive z (candidate.eval x₀) localRoot
    let specialization := integralBranchSpecialization localFactor z
      (localFactor.leadingCoeff.eval z * candidate.eval x₀) rootPair
    specialization
        (clearedFiniteBranchEvaluation globalFactor globalFactorPositive x₀
          localFactor root rootEquation rootConstant xBound x) =
      specialization
          (AdjoinRoot.of (integralLocalFactor localFactor)
            localFactor.leadingCoeff) *
        specialization
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent (xBound - 1) *
        (∑ order ∈ Finset.range xBound,
          (x - x₀) ^ order *
            PowerSeries.coeff order
              (shiftedCandidateSeries x₀ candidate)) := by
  classical
  dsimp only
  let rootPair := integralLocalFactor_root_of_localFactor_root localFactor
    localFactorPositive z (candidate.eval x₀) localRoot
  let specialization := integralBranchSpecialization localFactor z
    (localFactor.leadingCoeff.eval z * candidate.eval x₀) rootPair
  unfold clearedFiniteBranchEvaluation integralBranchScalar
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro order orderMem
  have orderLt : order < xBound := Finset.mem_range.mp orderMem
  have exponentLe := henselDenominatorExponent_le_of_lt orderLt
  have chosenSpecialized :=
    specialization_chosenRegularClearedHenselCoefficient globalFactor
      globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive root rootEquation rootConstant z candidate localRoot
      candidateRoot simple notPole order
  simp only [map_mul, map_pow]
  rw [integralBranchSpecialization_of, chosenSpecialized]
  have powerCombine :
      specialization
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          (henselDenominatorExponent (xBound - 1) -
            henselDenominatorExponent order) *
        specialization
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent order =
        specialization
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent (xBound - 1) := by
    rw [← pow_add, Nat.sub_add_cancel exponentLe]
  rw [Polynomial.eval_C, ← powerCombine]
  ring

/-- A finite Hasse/Taylor sum of length beyond the candidate degree evaluates
to the candidate at the unshifted point.  This is valid in finite
characteristic and uses no factorial denominators. -/
theorem sum_coeff_shiftedCandidateSeries_eq_eval
    (x₀ x : QM31Exact) (candidate : QM31Exact[X]) (xBound : Nat)
    (degreeLt : candidate.natDegree < xBound) :
    (∑ order ∈ Finset.range xBound,
        (x - x₀) ^ order *
          PowerSeries.coeff order (shiftedCandidateSeries x₀ candidate)) =
      candidate.eval x := by
  rw [shiftedCandidateSeries, shiftedEvaluationHom_eq_coe_taylor]
  simp_rw [Polynomial.coeff_coe]
  have degreeTaylor : (Polynomial.taylor x₀ candidate).natDegree < xBound :=
    (Polynomial.natDegree_taylor candidate x₀).trans_lt degreeLt
  calc
    (∑ order ∈ Finset.range xBound,
        (x - x₀) ^ order *
          (Polynomial.taylor x₀ candidate).coeff order) =
        (Polynomial.taylor x₀ candidate).eval (x - x₀) := by
          simpa only [mul_comm] using
            (Polynomial.eval_eq_sum_range' degreeTaylor (x - x₀)).symm
    _ = candidate.eval x :=
      Polynomial.taylor_eval_sub (r := x₀) (f := candidate) x

/-- The integral discrepancy between the one fixed finite branch and a
base-field polynomial in the challenge.  This is the element charged to one
resultant at a heavy domain coordinate. -/
def clearedFiniteBranchDiscrepancy
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
    (xBound : Nat) (x : QM31Exact) (received : QM31Exact[X]) :
    IntegralLocalBranch localFactor :=
  clearedFiniteBranchEvaluation globalFactor globalFactorPositive x₀
      localFactor root rootEquation rootConstant xBound x -
    AdjoinRoot.of (integralLocalFactor localFactor)
        localFactor.leadingCoeff *
      regularizedHenselDerivative globalFactor x₀ localFactor ^
        henselDenominatorExponent (xBound - 1) *
      AdjoinRoot.of (integralLocalFactor localFactor) received

/-- A support incidence makes the integral discrepancy specialize to zero.
The candidate and support remain challenge-dependent; cancellation is not
used in this direction. -/
theorem specialization_clearedFiniteBranchDiscrepancy_eq_zero
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
    (xBound : Nat) (degreeLt : candidate.natDegree < xBound)
    (x : QM31Exact) (received : QM31Exact[X])
    (agrees : candidate.eval x = received.eval z) :
    let rootPair := integralLocalFactor_root_of_localFactor_root localFactor
      localFactorPositive z (candidate.eval x₀) localRoot
    integralBranchSpecialization localFactor z
        (localFactor.leadingCoeff.eval z * candidate.eval x₀) rootPair
        (clearedFiniteBranchDiscrepancy globalFactor globalFactorPositive x₀
          localFactor root rootEquation rootConstant xBound x received) = 0 := by
  dsimp only
  rw [clearedFiniteBranchDiscrepancy, map_sub,
    specialization_clearedFiniteBranchEvaluation globalFactor
      globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive root rootEquation rootConstant z candidate localRoot
      candidateRoot simple notPole xBound x,
    map_mul, map_mul, map_pow, integralBranchSpecialization_of,
    integralBranchSpecialization_of,
    sum_coeff_shiftedCandidateSeries_eq_eval x₀ x candidate xBound degreeLt,
    agrees, sub_self]

/-- If the fixed integral discrepancy vanishes, the finite branch evaluation
really is the received base-field challenge polynomial in the selected
function field.  Nonzero leading and derivative clearing factors are proved
and cancelled explicitly. -/
theorem finiteBranchValue_eq_received_of_discrepancy_eq_zero
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
    (xBound : Nat) (x : QM31Exact) (received : QM31Exact[X])
    (discrepancyZero :
      clearedFiniteBranchDiscrepancy globalFactor globalFactorPositive x₀
        localFactor root rootEquation rootConstant xBound x received = 0) :
    (∑ order ∈ Finset.range xBound,
        regularCoefficientMap localFactor (C ((x - x₀) ^ order)) *
          PowerSeries.coeff order root) =
      regularCoefficientMap localFactor received := by
  have leadingNeZero : localFactor.leadingCoeff ≠ 0 :=
    mt Polynomial.leadingCoeff_eq_zero.mp localFactorNeZero
  have mappedLeadingNeZero :
      regularCoefficientMap localFactor localFactor.leadingCoeff ≠ 0 := by
    intro mappedZero
    exact leadingNeZero (regularCoefficientMap_injective localFactor <| by
      simpa only [map_zero] using mappedZero)
  have mappedEtaNeZero :
      integralBranchToFunctionField localFactor
          (regularizedHenselDerivative globalFactor x₀ localFactor) ≠ 0 := by
    intro mappedZero
    apply etaNeZero
    apply integralBranchToFunctionField_injective localFactor
      localFactorNeZero localFactorPositive
    simpa only [map_zero] using mappedZero
  have mappedDiscrepancy := congrArg
    (integralBranchToFunctionField localFactor) discrepancyZero
  rw [clearedFiniteBranchDiscrepancy, map_sub,
    integralBranchToFunctionField_clearedFiniteBranchEvaluation globalFactor
      globalFactorPositive x₀ localFactor root rootEquation rootConstant
      xBound x,
    map_mul, map_mul, map_pow, integralBranchToFunctionField_of,
    integralBranchToFunctionField_of, map_zero, sub_eq_zero] at mappedDiscrepancy
  have commonNeZero :
      regularCoefficientMap localFactor localFactor.leadingCoeff *
          integralBranchToFunctionField localFactor
              (regularizedHenselDerivative globalFactor x₀ localFactor) ^
            henselDenominatorExponent (xBound - 1) ≠ 0 :=
    mul_ne_zero mappedLeadingNeZero (pow_ne_zero _ mappedEtaNeZero)
  apply mul_left_cancel₀ commonNeZero
  simpa only [mul_assoc, map_sub, map_pow] using mappedDiscrepancy

/-- Once one coordinate discrepancy has been killed as a regular function,
every simple pole-free specialization on the fixed branch agrees at that
coordinate—not only the support incidences used to prove the zero. -/
theorem candidate_eval_eq_received_of_discrepancy_eq_zero
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
    (xBound : Nat) (degreeLt : candidate.natDegree < xBound)
    (x : QM31Exact) (received : QM31Exact[X])
    (discrepancyZero :
      clearedFiniteBranchDiscrepancy globalFactor globalFactorPositive x₀
        localFactor root rootEquation rootConstant xBound x received = 0) :
    candidate.eval x = received.eval z := by
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
  have leadingEvalNeZero : localFactor.leadingCoeff.eval z ≠ 0 := by
    intro leadingZero
    exact notPole
      ((mem_localPoleChallengeSet_iff localFactor localFactorNeZero z).mpr
        leadingZero)
  have specializedZero := congrArg specialization discrepancyZero
  rw [clearedFiniteBranchDiscrepancy, map_sub,
    specialization_clearedFiniteBranchEvaluation globalFactor
      globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive root rootEquation rootConstant z candidate localRoot
      candidateRoot simple notPole xBound x,
    map_mul, map_mul, map_pow, integralBranchSpecialization_of,
    integralBranchSpecialization_of,
    sum_coeff_shiftedCandidateSeries_eq_eval x₀ x candidate xBound degreeLt,
    map_zero, sub_eq_zero] at specializedZero
  have commonNeZero :
      localFactor.leadingCoeff.eval z *
          specialization
              (regularizedHenselDerivative globalFactor x₀ localFactor) ^
            henselDenominatorExponent (xBound - 1) ≠ 0 :=
    mul_ne_zero leadingEvalNeZero
      (pow_ne_zero _ etaSpecializationNeZero)
  apply mul_left_cancel₀ commonNeZero
  simpa only [mul_assoc] using specializedZero

/-- Exact regular-function weight of the common-denominator finite branch
evaluation.  Every Taylor coefficient is charged to its own denominator
exponent, then raised only to the common maximum; this is the additive branch
budget used by BCH+25, not a uniform worst-factor assumption. -/
theorem integralBranchIteratedWeight_clearedFiniteBranchEvaluation_le
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
    (xBound : Nat) (x : QM31Exact) :
    let generatorWeight :=
      localBound + ell - ell * localFactor.natDegree
    let etaWeight := (parentBound - ell) +
      (globalFactor.natDegree - 1) *
        (localBound - ell * localFactor.natDegree)
    integralBranchIteratedWeight localFactor localFactorNeZero generatorWeight
        (clearedFiniteBranchEvaluation globalFactor globalFactorPositive x₀
          localFactor root rootEquation rootConstant xBound x) ≤
      generatorWeight +
        henselDenominatorExponent (xBound - 1) * etaWeight := by
  classical
  dsimp only
  let generatorWeight := localBound + ell - ell * localFactor.natDegree
  let etaWeight := (parentBound - ell) +
    (globalFactor.natDegree - 1) *
      (localBound - ell * localFactor.natDegree)
  have parentCoefficientBound : ∀ exponent ∈
      (specializeEvaluationPoint x₀ globalFactor).support,
      ((specializeEvaluationPoint x₀ globalFactor).coeff exponent).natDegree +
        ell * exponent ≤ parentBound := by
    intro exponent exponentMem
    have globalMem : exponent ∈ globalFactor.support := by
      rw [Polynomial.mem_support_iff] at exponentMem ⊢
      intro coefficientZero
      apply exponentMem
      simp [specializeEvaluationPoint, coefficientZero]
    exact (Nat.add_le_add_right
      (by
        simpa [specializeEvaluationPoint, evaluateInnerVariable] using
          (Polynomial.natDegree_map_le
            (p := globalFactor.coeff exponent)
            (f := Polynomial.evalRingHom x₀))) (ell * exponent)).trans
      (globalCoefficientBound exponent globalMem)
  have etaBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          generatorWeight
          (regularizedHenselDerivative globalFactor x₀ localFactor) ≤
        etaWeight := by
    exact integralBranchIteratedWeight_regularizedHenselDerivative_le
      globalFactor x₀ localFactor localFactorNeZero ell localBound parentBound
        localCoefficientBound parentCoefficientBound
  unfold clearedFiniteBranchEvaluation
  apply integralBranchIteratedWeight_finset_sum_le localFactor
    localFactorNeZero generatorWeight
      (generatorWeight +
        henselDenominatorExponent (xBound - 1) * etaWeight)
  intro order orderMem
  have orderLt : order < xBound := Finset.mem_range.mp orderMem
  have exponentLe := henselDenominatorExponent_le_of_lt orderLt
  have scalarBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          generatorWeight
          (integralBranchScalar localFactor ((x - x₀) ^ order)) ≤ 0 := by
    unfold integralBranchScalar
    simpa using integralBranchIteratedWeight_of_le_natDegree localFactor
      localFactorNeZero ell localBound localCoefficientBound
      (C ((x - x₀) ^ order))
  have etaPowerBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          generatorWeight
          (regularizedHenselDerivative globalFactor x₀ localFactor ^
            (henselDenominatorExponent (xBound - 1) -
              henselDenominatorExponent order)) ≤
        (henselDenominatorExponent (xBound - 1) -
            henselDenominatorExponent order) * etaWeight :=
    (integralBranchIteratedWeight_pow_le localFactor localFactorNeZero ell
      localBound localCoefficientBound
      (regularizedHenselDerivative globalFactor x₀ localFactor) _).trans
        (Nat.mul_le_mul_left _ etaBound)
  have coefficientBound :=
    chosenRegularClearedHenselCoefficient_weight_le globalFactor
      globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive ell localBound parentBound ellLeParent
      localCoefficientBound globalCoefficientBound root rootEquation
      rootConstant order
  calc
    integralBranchIteratedWeight localFactor localFactorNeZero generatorWeight
        (integralBranchScalar localFactor ((x - x₀) ^ order) *
          regularizedHenselDerivative globalFactor x₀ localFactor ^
            (henselDenominatorExponent (xBound - 1) -
              henselDenominatorExponent order) *
          chosenRegularClearedHenselCoefficient globalFactor
            globalFactorPositive x₀ localFactor root rootEquation rootConstant
              order) ≤
        integralBranchIteratedWeight localFactor localFactorNeZero
            generatorWeight
            (integralBranchScalar localFactor ((x - x₀) ^ order)) +
          integralBranchIteratedWeight localFactor localFactorNeZero
            generatorWeight
            (regularizedHenselDerivative globalFactor x₀ localFactor ^
                (henselDenominatorExponent (xBound - 1) -
                  henselDenominatorExponent order) *
              chosenRegularClearedHenselCoefficient globalFactor
                globalFactorPositive x₀ localFactor root rootEquation
                  rootConstant order) :=
      by
        simpa only [mul_assoc, generatorWeight] using
          (integralBranchIteratedWeight_mul_le localFactor
            localFactorNeZero ell localBound localCoefficientBound
            (integralBranchScalar localFactor ((x - x₀) ^ order))
            (regularizedHenselDerivative globalFactor x₀ localFactor ^
                (henselDenominatorExponent (xBound - 1) -
                  henselDenominatorExponent order) *
              chosenRegularClearedHenselCoefficient globalFactor
                globalFactorPositive x₀ localFactor root rootEquation
                  rootConstant order))
    _ ≤ 0 +
        ((henselDenominatorExponent (xBound - 1) -
              henselDenominatorExponent order) * etaWeight +
          (generatorWeight +
            henselDenominatorExponent order * etaWeight)) := by
      gcongr
      exact (integralBranchIteratedWeight_mul_le localFactor
        localFactorNeZero ell localBound localCoefficientBound _ _).trans
          (Nat.add_le_add etaPowerBound coefficientBound)
    _ = generatorWeight +
        henselDenominatorExponent (xBound - 1) * etaWeight := by
      rw [zero_add]
      calc
        (henselDenominatorExponent (xBound - 1) -
              henselDenominatorExponent order) * etaWeight +
            (generatorWeight +
              henselDenominatorExponent order * etaWeight) =
            generatorWeight +
              ((henselDenominatorExponent (xBound - 1) -
                  henselDenominatorExponent order) +
                henselDenominatorExponent order) * etaWeight := by ring
        _ = generatorWeight +
            henselDenominatorExponent (xBound - 1) * etaWeight := by
          rw [Nat.sub_add_cancel exponentLe]

/-- A small weight-composition lemma kept separate from the concrete Hensel
objects so elaboration of the terminal branch budget does not repeatedly
normalize their dependent quotient types. -/
theorem integralBranchIteratedWeight_sub_triple_le
    (localFactor : BivariatePolynomial QM31Exact)
    (localFactorNeZero : localFactor ≠ 0)
    (ell localBound target
      leadingBound etaBound receivedBound : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (branch leading eta received : IntegralLocalBranch localFactor)
    (branchWeight : integralBranchIteratedWeight localFactor
      localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree) branch ≤ target)
    (leadingWeight : integralBranchIteratedWeight localFactor
      localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree) leading ≤ leadingBound)
    (etaWeight : integralBranchIteratedWeight localFactor
      localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree) eta ≤ etaBound)
    (receivedWeight : integralBranchIteratedWeight localFactor
      localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree) received ≤ receivedBound)
    (sumBound : leadingBound + etaBound + receivedBound ≤ target) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (branch - leading * eta * received) ≤ target := by
  have leadingEta := integralBranchIteratedWeight_mul_le localFactor
    localFactorNeZero ell localBound localCoefficientBound leading eta
  have triple := integralBranchIteratedWeight_mul_le localFactor
    localFactorNeZero ell localBound localCoefficientBound
      (leading * eta) received
  have tripleWeight : integralBranchIteratedWeight localFactor
      localFactorNeZero (localBound + ell - ell * localFactor.natDegree)
        (leading * eta * received) ≤ target :=
    triple.trans <| (Nat.add_le_add
      (leadingEta.trans (Nat.add_le_add leadingWeight etaWeight))
      receivedWeight).trans sumBound
  rw [sub_eq_add_neg]
  exact (integralBranchIteratedWeight_add_le localFactor localFactorNeZero
    (localBound + ell - ell * localFactor.natDegree) _ _).trans <|
      max_le branchWeight (by
      rw [integralBranchIteratedWeight_neg]
      exact tripleWeight)

/-- Adding the received challenge polynomial costs no more than the same
branch budget when its degree is at most the released message bound `ell`.
This is the exact element to which the root-pair zero count is applied. -/
theorem integralBranchIteratedWeight_clearedFiniteBranchDiscrepancy_le
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
    (xBound : Nat) (x : QM31Exact) (received : QM31Exact[X])
    (receivedDegree : received.natDegree ≤ ell) :
    let generatorWeight :=
      localBound + ell - ell * localFactor.natDegree
    let etaWeight := (parentBound - ell) +
      (globalFactor.natDegree - 1) *
        (localBound - ell * localFactor.natDegree)
    integralBranchIteratedWeight localFactor localFactorNeZero generatorWeight
        (clearedFiniteBranchDiscrepancy globalFactor globalFactorPositive x₀
          localFactor root rootEquation rootConstant xBound x received) ≤
      generatorWeight +
        henselDenominatorExponent (xBound - 1) * etaWeight := by
  dsimp only
  let generatorWeight := localBound + ell - ell * localFactor.natDegree
  let etaWeight := (parentBound - ell) +
    (globalFactor.natDegree - 1) *
      (localBound - ell * localFactor.natDegree)
  have branchBound :=
    integralBranchIteratedWeight_clearedFiniteBranchEvaluation_le
      globalFactor globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive ell localBound parentBound ellLeParent
      localCoefficientBound globalCoefficientBound root rootEquation
      rootConstant xBound x
  have leadingMem : localFactor.natDegree ∈ localFactor.support :=
    Polynomial.natDegree_mem_support_of_nonzero localFactorNeZero
  have leadingBound := localCoefficientBound localFactor.natDegree leadingMem
  change localFactor.leadingCoeff.natDegree +
      ell * localFactor.natDegree ≤ localBound at leadingBound
  have embeddedLeadingBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          generatorWeight
          (AdjoinRoot.of (integralLocalFactor localFactor)
            localFactor.leadingCoeff) ≤
        localBound - ell * localFactor.natDegree :=
    (integralBranchIteratedWeight_of_le_natDegree localFactor
      localFactorNeZero ell localBound localCoefficientBound
      localFactor.leadingCoeff).trans (by omega)
  have etaBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          generatorWeight
          (regularizedHenselDerivative globalFactor x₀ localFactor) ≤
        etaWeight := by
    have parentCoefficientBound : ∀ exponent ∈
        (specializeEvaluationPoint x₀ globalFactor).support,
        ((specializeEvaluationPoint x₀ globalFactor).coeff exponent).natDegree +
          ell * exponent ≤ parentBound := by
      intro exponent exponentMem
      have globalMem : exponent ∈ globalFactor.support := by
        rw [Polynomial.mem_support_iff] at exponentMem ⊢
        intro coefficientZero
        apply exponentMem
        simp [specializeEvaluationPoint, coefficientZero]
      exact (Nat.add_le_add_right
        (by
          simpa [specializeEvaluationPoint, evaluateInnerVariable] using
            (Polynomial.natDegree_map_le
              (p := globalFactor.coeff exponent)
              (f := Polynomial.evalRingHom x₀))) (ell * exponent)).trans
        (globalCoefficientBound exponent globalMem)
    exact integralBranchIteratedWeight_regularizedHenselDerivative_le
      globalFactor x₀ localFactor localFactorNeZero ell localBound parentBound
        localCoefficientBound parentCoefficientBound
  have etaPowerBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          generatorWeight
          (regularizedHenselDerivative globalFactor x₀ localFactor ^
            henselDenominatorExponent (xBound - 1)) ≤
        henselDenominatorExponent (xBound - 1) * etaWeight :=
    (integralBranchIteratedWeight_pow_le localFactor localFactorNeZero ell
      localBound localCoefficientBound
      (regularizedHenselDerivative globalFactor x₀ localFactor) _).trans
        (Nat.mul_le_mul_left _ etaBound)
  have receivedBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          generatorWeight
          (AdjoinRoot.of (integralLocalFactor localFactor) received) ≤ ell :=
    (integralBranchIteratedWeight_of_le_natDegree localFactor
      localFactorNeZero ell localBound localCoefficientBound received).trans
        receivedDegree
  unfold clearedFiniteBranchDiscrepancy
  apply integralBranchIteratedWeight_sub_triple_le localFactor
    localFactorNeZero ell localBound
    (generatorWeight +
      henselDenominatorExponent (xBound - 1) * etaWeight)
    (localBound - ell * localFactor.natDegree)
    (henselDenominatorExponent (xBound - 1) * etaWeight) ell
    localCoefficientBound
  · exact branchBound
  · exact embeddedLeadingBound
  · exact etaPowerBound
  · exact receivedBound
  · dsimp [generatorWeight]
    omega

/-- More support incidences than the exact fixed-branch resultant budget
force the branch value at one domain coordinate to equal that coordinate's
received challenge polynomial.  Candidates and their local root values may
still vary independently with the challenge. -/
theorem finiteBranchValue_eq_received_of_many_agreements
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
    (xBound : Nat)
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
      (candidate z).natDegree < xBound)
    (x : QM31Exact) (received : QM31Exact[X])
    (receivedDegree : received.natDegree ≤ ell)
    (agrees : ∀ z ∈ challenges,
      (candidate z).eval x = received.eval z)
    (tooMany :
      localFactor.natDegree *
          ((localBound + ell - ell * localFactor.natDegree) +
            henselDenominatorExponent (xBound - 1) *
              ((parentBound - ell) + (globalFactor.natDegree - 1) *
                (localBound - ell * localFactor.natDegree))) <
        challenges.card) :
    clearedFiniteBranchDiscrepancy globalFactor globalFactorPositive x₀
          localFactor root rootEquation rootConstant xBound x received = 0 ∧
      (∑ order ∈ Finset.range xBound,
          regularCoefficientMap localFactor (C ((x - x₀) ^ order)) *
            PowerSeries.coeff order root) =
        regularCoefficientMap localFactor received := by
  let discrepancy := clearedFiniteBranchDiscrepancy globalFactor
    globalFactorPositive x₀ localFactor root rootEquation rootConstant
      xBound x received
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
          (rootPair z zMem) discrepancy = 0 := by
    intro z zMem
    exact specialization_clearedFiniteBranchDiscrepancy_eq_zero globalFactor
      globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive root rootEquation rootConstant z (candidate z)
      (localRoot z zMem) (candidateRoot z zMem) (simple z zMem)
      (notPole z zMem) xBound (candidateDegree z zMem) x received
      (agrees z zMem)
  have discrepancyWeight :=
    integralBranchIteratedWeight_clearedFiniteBranchDiscrepancy_le
      globalFactor globalFactorPositive x₀ localFactor localFactorNeZero
      localFactorPositive ell localBound parentBound ellLeParent
      localCoefficientBound globalCoefficientBound root rootEquation
      rootConstant xBound x received receivedDegree
  have discrepancyZero : discrepancy = 0 := by
    apply integralBranch_eq_zero_of_mul_weight_lt_card localFactor
      localFactorNeZero localFactorPositive ell localBound
      localCoefficientBound discrepancy challenges rootValue rootPair
      specializationZero
    exact (Nat.mul_le_mul_left localFactor.natDegree
      discrepancyWeight).trans_lt tooMany
  refine ⟨discrepancyZero, ?_⟩
  exact finiteBranchValue_eq_received_of_discrepancy_eq_zero globalFactor
    globalFactorPositive x₀ localFactor localFactorNeZero localFactorPositive
    root rootEquation rootConstant etaNeZero xBound x received discrepancyZero

#print axioms henselDenominatorExponent_le_of_lt
#print axioms integralBranchToFunctionField_clearedFiniteBranchEvaluation
#print axioms specialization_clearedFiniteBranchEvaluation
#print axioms sum_coeff_shiftedCandidateSeries_eq_eval
#print axioms specialization_clearedFiniteBranchDiscrepancy_eq_zero
#print axioms finiteBranchValue_eq_received_of_discrepancy_eq_zero
#print axioms candidate_eval_eq_received_of_discrepancy_eq_zero
#print axioms integralBranchIteratedWeight_clearedFiniteBranchEvaluation_le
#print axioms integralBranchIteratedWeight_sub_triple_le
#print axioms integralBranchIteratedWeight_clearedFiniteBranchDiscrepancy_le
#print axioms finiteBranchValue_eq_received_of_many_agreements

end

end AspisK1.V7ExactCorrelatedAgreementBranchEvaluation
