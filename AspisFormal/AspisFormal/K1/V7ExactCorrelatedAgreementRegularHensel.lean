import AspisFormal.K1.V7ExactCorrelatedAgreementRegularEvaluation

/-!
# The concrete regular Hensel derivative for V7

This file constructs the denominator-free derivative coefficient used by the
implicit-function recurrence.  Its nonvanishing is proved from the explicit
finite-characteristic separability certificate for the already-fixed local
branch.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementRegularHensel

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementRegularEvaluation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Challenges at which the fixed local branch has a pole in the rational
`Y=T/W` presentation. -/
noncomputable def localPoleChallengeSet
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K) : Finset K := by
  classical
  exact localFactor.leadingCoeff.roots.toFinset

theorem mem_localPoleChallengeSet_iff
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (z : K) :
    z ∈ localPoleChallengeSet localFactor ↔
      localFactor.leadingCoeff.eval z = 0 := by
  classical
  have leadingNeZero : localFactor.leadingCoeff ≠ 0 :=
    mt Polynomial.leadingCoeff_eq_zero.mp localFactorNeZero
  simp [localPoleChallengeSet, Polynomial.mem_roots leadingNeZero,
    Polynomial.IsRoot]

/-- Pole challenges are counted explicitly by the `Z`-degree of `W`; they
are never passed to a specialization map that divides by `W(z)`. -/
theorem localPoleChallengeSet_card_le
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K) :
    (localPoleChallengeSet localFactor).card ≤
      localFactor.leadingCoeff.natDegree := by
  classical
  unfold localPoleChallengeSet
  exact (Multiset.toFinset_card_le localFactor.leadingCoeff.roots).trans
    (Polynomial.card_roots' localFactor.leadingCoeff)

/-- `W^(d-1) * ∂R/∂Y(x₀,T/W,Z)` as an element of the actual integral
local quotient.  It is `W*ξ` in the notation of BCIKS Appendix A.4. -/
def regularizedHenselDerivative
    {K : Type*} [Field K] (globalFactor : TrivariatePolynomial K) (x₀ : K)
    (localFactor : BivariatePolynomial K) : IntegralLocalBranch localFactor :=
  regularizedBranchEvaluation localFactor
    (specializeEvaluationPoint x₀ globalFactor).derivative
    (globalFactor.natDegree - 1)

theorem specializedDerivative_natDegree_le_global_sub_one
    {K : Type*} [Field K] (globalFactor : TrivariatePolynomial K) (x₀ : K) :
    (specializeEvaluationPoint x₀ globalFactor).derivative.natDegree ≤
      globalFactor.natDegree - 1 := by
  exact (Polynomial.natDegree_derivative_le _).trans <|
    Nat.sub_le_sub_right Polynomial.natDegree_map_le 1

/-- The regular derivative maps to the literal scaled derivative value in the
fixed branch field. -/
theorem integralBranchToFunctionField_regularizedHenselDerivative
    {K : Type*} [Field K] (globalFactor : TrivariatePolynomial K) (x₀ : K)
    (localFactor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational localFactor))] :
    integralBranchToFunctionField localFactor
        (regularizedHenselDerivative globalFactor x₀ localFactor) =
      regularCoefficientMap localFactor localFactor.leadingCoeff ^
          (globalFactor.natDegree - 1) *
        (specializeEvaluationPoint x₀ globalFactor).derivative.eval₂
          (regularCoefficientMap localFactor)
          (AdjoinRoot.root (localFactorOverRational localFactor)) := by
  exact integralBranchToFunctionField_regularizedBranchEvaluation localFactor
    (specializeEvaluationPoint x₀ globalFactor).derivative
    (globalFactor.natDegree - 1)
    (specializedDerivative_natDegree_le_global_sub_one globalFactor x₀)

/-- Exact nonvanishing of the Hensel derivative in characteristic `P`.  The
proof uses the explicit resultant certificate at `x₀`; no characteristic-zero
derivative heuristic and no specialization-level factor choice occurs. -/
theorem exactV7_regularizedHenselDerivative_ne_zero
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
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
    regularizedHenselDerivative globalFactor x₀ localFactor ≠ 0 := by
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
  have localFactorNeZero : localFactor ≠ 0 :=
    (bivariatePrimeFactors_prime parent parentNeZero localFactor
      localFactorMem).ne_zero
  have leadingNeZero : localFactor.leadingCoeff ≠ 0 :=
    mt Polynomial.leadingCoeff_eq_zero.mp localFactorNeZero
  have mappedLeadingNeZero :
      regularCoefficientMap localFactor localFactor.leadingCoeff ≠ 0 := by
    intro mappedZero
    exact leadingNeZero (regularCoefficientMap_injective localFactor <| by
      simpa using mappedZero)
  have derivativeValueNeZero :
      parent.derivative.eval₂ (regularCoefficientMap localFactor)
          (AdjoinRoot.root (localFactorOverRational localFactor)) ≠ 0 := by
    rw [Polynomial.eval₂_eq_eval_map]
    simpa [Polynomial.IsRoot, regularCoefficientMap, Polynomial.map_map,
      parent] using
      (localBranchRoot_not_isRoot_parentDerivative globalFactor x₀
        certificateAtPoint localFactor localFactorMem localFactorPositive)
  intro derivativeZero
  have mappedZero := congrArg (integralBranchToFunctionField localFactor)
    derivativeZero
  rw [integralBranchToFunctionField_regularizedHenselDerivative,
    map_zero] at mappedZero
  exact (mul_ne_zero (pow_ne_zero _ mappedLeadingNeZero)
    derivativeValueNeZero) mappedZero

/-- Away from the explicitly counted poles, a challenge-dependent simple
root sees a nonzero specialization of the regular Hensel derivative. -/
theorem specialization_regularizedHenselDerivative_ne_zero
    {K : Type*} [Field K]
    (globalFactor : TrivariatePolynomial K) (x₀ z : K)
    (localFactor : BivariatePolynomial K) (localFactorNeZero : localFactor ≠ 0)
    (localFactorPositive : 0 < localFactor.natDegree)
    (candidate : K[X])
    (localRoot : localFactor.eval₂ (Polynomial.evalRingHom z)
      (candidate.eval x₀) = 0)
    (simple : SimpleSpecializedRoot globalFactor x₀ z candidate)
    (notPole : z ∉ localPoleChallengeSet localFactor) :
    integralBranchSpecialization localFactor z
        (localFactor.leadingCoeff.eval z * candidate.eval x₀)
        (integralLocalFactor_root_of_localFactor_root localFactor
          localFactorPositive z (candidate.eval x₀) localRoot)
        (regularizedHenselDerivative globalFactor x₀ localFactor) ≠ 0 := by
  have leadingAtChallengeNeZero : localFactor.leadingCoeff.eval z ≠ 0 := by
    exact fun leadingZero => notPole
      ((mem_localPoleChallengeSet_iff localFactor localFactorNeZero z).mpr
        leadingZero)
  have derivativeAtChallengeNeZero :
      (specializeEvaluationPoint x₀ globalFactor).derivative.eval₂
          (Polynomial.evalRingHom z) (candidate.eval x₀) ≠ 0 := by
    intro derivativeZero
    apply simple.2
    have specializedDerivative :
        specializeEvaluationPoint x₀ globalFactor.derivative =
          (specializeEvaluationPoint x₀ globalFactor).derivative := by
      change globalFactor.derivative.map (evaluateInnerVariable x₀) =
        (globalFactor.map (evaluateInnerVariable x₀)).derivative
      rw [Polynomial.derivative_map]
    rw [Polynomial.IsRoot, ← specializeEvaluationPointChallenge_derivative]
    change ((specializeEvaluationPoint x₀ globalFactor.derivative).map
      (Polynomial.evalRingHom z)).eval (candidate.eval x₀) = 0
    rw [Polynomial.eval_map]
    rw [specializedDerivative]
    exact derivativeZero
  rw [regularizedHenselDerivative]
  rw [integralBranchSpecialization_regularizedBranchEvaluation localFactor
    (specializeEvaluationPoint x₀ globalFactor).derivative
    (globalFactor.natDegree - 1)
    (specializedDerivative_natDegree_le_global_sub_one globalFactor x₀)
    z (candidate.eval x₀) localFactorPositive localRoot]
  exact mul_ne_zero (pow_ne_zero _ leadingAtChallengeNeZero)
    derivativeAtChallengeNeZero

#print axioms integralBranchToFunctionField_regularizedHenselDerivative
#print axioms exactV7_regularizedHenselDerivative_ne_zero
#print axioms mem_localPoleChallengeSet_iff
#print axioms localPoleChallengeSet_card_le
#print axioms specialization_regularizedHenselDerivative_ne_zero

end

end AspisK1.V7ExactCorrelatedAgreementRegularHensel
