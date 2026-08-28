import AspisFormal.K1.V7ExactCorrelatedAgreementHenselCombinatorics

/-!
# Denominator-free evaluation on the exact integral V7 branch

If `P(Y,Z)` has `Y`-degree at most `d`, then

`W^(d-deg P) * scaleRoots(P,W)`

is the literal polynomial `W^d P(T/W,Z)`.  This module evaluates that
polynomial in the integral quotient at `T`, and proves that its image in the
fixed function field is exactly `W^d P(Y,Z)`.  The construction performs no
division and therefore remains meaningful at specializations where `W(z)=0`.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementRegularEvaluation

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementRegularWeights

noncomputable section

/-- The denominator-free value `W^d P(T/W,Z)` in the actual integral
quotient. -/
def regularizedBranchEvaluation
    {K : Type*} [Field K] (factor polynomial : BivariatePolynomial K)
    (outerDegree : Nat) : IntegralLocalBranch factor :=
  AdjoinRoot.of (integralLocalFactor factor)
      (factor.leadingCoeff ^ (outerDegree - polynomial.natDegree)) *
    AdjoinRoot.mk (integralLocalFactor factor)
      (polynomial.scaleRoots factor.leadingCoeff)

/-- Mapping the denominator-free value into the fixed function field gives
the expected scaled rational evaluation.  This is the exact algebraic bridge
used for every shifted-X coefficient in the Hensel recurrence. -/
theorem integralBranchToFunctionField_regularizedBranchEvaluation
    {K : Type*} [Field K] (factor polynomial : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))]
    (outerDegree : Nat) (degreeLe : polynomial.natDegree ≤ outerDegree) :
    integralBranchToFunctionField factor
        (regularizedBranchEvaluation factor polynomial outerDegree) =
      regularCoefficientMap factor factor.leadingCoeff ^ outerDegree *
        polynomial.eval₂ (regularCoefficientMap factor)
          (AdjoinRoot.root (localFactorOverRational factor)) := by
  let coefficientMap := regularCoefficientMap factor
  let branchRoot := AdjoinRoot.root (localFactorOverRational factor)
  rw [regularizedBranchEvaluation, map_mul,
    integralBranchToFunctionField_of]
  unfold integralBranchToFunctionField
  rw [AdjoinRoot.lift_mk]
  change coefficientMap
        (factor.leadingCoeff ^ (outerDegree - polynomial.natDegree)) *
      (polynomial.scaleRoots factor.leadingCoeff).eval₂ coefficientMap
        (integralBranchGenerator factor) = _
  rw [map_pow]
  change coefficientMap factor.leadingCoeff ^
        (outerDegree - polynomial.natDegree) *
      (polynomial.scaleRoots factor.leadingCoeff).eval₂ coefficientMap
        (coefficientMap factor.leadingCoeff * branchRoot) = _
  rw [Polynomial.scaleRoots_eval₂_mul]
  rw [← mul_assoc, ← pow_add]
  rw [Nat.sub_add_cancel degreeLe]

/-- If the original bivariate polynomial vanishes at `(y,z)`, its regularized
value vanishes under the integral root-pair specialization
`T = W(z)y`.  No nonvanishing assumption on `W(z)` is used. -/
theorem integralBranchSpecialization_regularizedBranchEvaluation_eq_zero
    {K : Type*} [Field K] (factor polynomial : BivariatePolynomial K)
    (outerDegree : Nat) (_degreeLe : polynomial.natDegree ≤ outerDegree)
    (z y : K)
    (factorPositive : 0 < factor.natDegree)
    (factorRoot : factor.eval₂ (Polynomial.evalRingHom z) y = 0)
    (polynomialRoot : polynomial.eval₂ (Polynomial.evalRingHom z) y = 0) :
    integralBranchSpecialization factor z
        (factor.leadingCoeff.eval z * y)
        (integralLocalFactor_root_of_localFactor_root factor factorPositive
          z y factorRoot)
        (regularizedBranchEvaluation factor polynomial outerDegree) = 0 := by
  let evaluation := Polynomial.evalRingHom z
  let t := factor.leadingCoeff.eval z * y
  let rootPair := integralLocalFactor_root_of_localFactor_root factor
    factorPositive z y factorRoot
  rw [regularizedBranchEvaluation, map_mul,
    integralBranchSpecialization_of]
  unfold integralBranchSpecialization
  rw [AdjoinRoot.lift_mk]
  change evaluation
        (factor.leadingCoeff ^ (outerDegree - polynomial.natDegree)) *
      (polynomial.scaleRoots factor.leadingCoeff).eval₂ evaluation t = 0
  rw [map_pow]
  change (evaluation factor.leadingCoeff) ^
        (outerDegree - polynomial.natDegree) *
      (polynomial.scaleRoots factor.leadingCoeff).eval₂ evaluation
        (evaluation factor.leadingCoeff * y) = 0
  rw [Polynomial.scaleRoots_eval₂_mul, polynomialRoot, mul_zero, mul_zero]

/-- Full specialization identity behind the preceding zero statement. -/
theorem integralBranchSpecialization_regularizedBranchEvaluation
    {K : Type*} [Field K] (factor polynomial : BivariatePolynomial K)
    (outerDegree : Nat) (degreeLe : polynomial.natDegree ≤ outerDegree)
    (z y : K)
    (factorPositive : 0 < factor.natDegree)
    (factorRoot : factor.eval₂ (Polynomial.evalRingHom z) y = 0) :
    integralBranchSpecialization factor z
        (factor.leadingCoeff.eval z * y)
        (integralLocalFactor_root_of_localFactor_root factor factorPositive
          z y factorRoot)
        (regularizedBranchEvaluation factor polynomial outerDegree) =
      factor.leadingCoeff.eval z ^ outerDegree *
        polynomial.eval₂ (Polynomial.evalRingHom z) y := by
  let evaluation := Polynomial.evalRingHom z
  rw [regularizedBranchEvaluation, map_mul,
    integralBranchSpecialization_of]
  unfold integralBranchSpecialization
  rw [AdjoinRoot.lift_mk]
  change evaluation
        (factor.leadingCoeff ^ (outerDegree - polynomial.natDegree)) *
      (polynomial.scaleRoots factor.leadingCoeff).eval₂ evaluation
          (evaluation factor.leadingCoeff * y) = _
  rw [map_pow, Polynomial.scaleRoots_eval₂_mul]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel degreeLe]
  rfl

/-! ## Exact weight of denominator-free evaluation -/

/-- Coefficientwise weight bound for `W^d P(T/W,Z)`.  The generator weight
is `wBound + ell`, while `deg W ≤ wBound`; hence the `T` exponent and the
removed powers of `W` cancel exactly. -/
theorem regularizedPolynomial_iteratedWeight_le
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K)
    (leading : Polynomial K)
    (outerDegree ell polynomialBound wBound : Nat)
    (degreeLe : polynomial.natDegree ≤ outerDegree)
    (leadingDegree : leading.natDegree ≤ wBound)
    (coefficientBound : ∀ exponent ∈ polynomial.support,
      (polynomial.coeff exponent).natDegree + ell * exponent ≤
        polynomialBound) :
    iteratedBivariateWeight (wBound + ell)
        (C (leading ^ (outerDegree - polynomial.natDegree)) *
          polynomial.scaleRoots leading) ≤
      polynomialBound + outerDegree * wBound := by
  apply iteratedBivariateWeight_le_of_coeff
  intro exponent exponentMem
  have coefficientNeZero :
      (C (leading ^ (outerDegree - polynomial.natDegree)) *
        polynomial.scaleRoots leading).coeff exponent ≠ 0 :=
    Polynomial.mem_support_iff.mp exponentMem
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_scaleRoots] at coefficientNeZero ⊢
  have originalCoefficientNeZero : polynomial.coeff exponent ≠ 0 := by
    exact fun coefficientZero => coefficientNeZero (by simp [coefficientZero])
  have exponentLe : exponent ≤ polynomial.natDegree :=
    Polynomial.le_natDegree_of_ne_zero originalCoefficientNeZero
  have originalBound := coefficientBound exponent
    (Polynomial.mem_support_iff.mpr originalCoefficientNeZero)
  have degreeProduct :
      (leading ^ (outerDegree - polynomial.natDegree) *
        (polynomial.coeff exponent *
          leading ^ (polynomial.natDegree - exponent))).natDegree ≤
        (outerDegree - polynomial.natDegree) * leading.natDegree +
          ((polynomial.coeff exponent).natDegree +
            (polynomial.natDegree - exponent) * leading.natDegree) := by
    exact Polynomial.natDegree_mul_le.trans <| Nat.add_le_add
      Polynomial.natDegree_pow_le
      (Polynomial.natDegree_mul_le.trans <| Nat.add_le_add_left
        Polynomial.natDegree_pow_le _)
  have weightParts :
      (outerDegree - polynomial.natDegree) * wBound +
          (polynomial.natDegree - exponent) * wBound +
            exponent * wBound = outerDegree * wBound := by
    calc
      (outerDegree - polynomial.natDegree) * wBound +
          (polynomial.natDegree - exponent) * wBound +
            exponent * wBound =
          ((outerDegree - polynomial.natDegree) +
            (polynomial.natDegree - exponent) + exponent) * wBound := by
              ring
      _ = outerDegree * wBound := by
        congr 1
        omega
  calc
    (leading ^ (outerDegree - polynomial.natDegree) *
          (polynomial.coeff exponent *
            leading ^ (polynomial.natDegree - exponent))).natDegree +
        exponent * (wBound + ell) ≤
      ((outerDegree - polynomial.natDegree) * leading.natDegree +
        ((polynomial.coeff exponent).natDegree +
          (polynomial.natDegree - exponent) * leading.natDegree)) +
        exponent * (wBound + ell) := Nat.add_le_add_right degreeProduct _
    _ ≤ ((outerDegree - polynomial.natDegree) * wBound +
        ((polynomial.coeff exponent).natDegree +
          (polynomial.natDegree - exponent) * wBound)) +
        exponent * (wBound + ell) := by gcongr
    _ = ((polynomial.coeff exponent).natDegree + ell * exponent) +
        outerDegree * wBound := by
      rw [Nat.mul_add, Nat.mul_comm exponent ell]
      omega
    _ ≤ polynomialBound + outerDegree * wBound :=
      Nat.add_le_add_right originalBound _

/-- The same bound for the actual quotient element.  The leading-coefficient
budget is derived from the local factor's own weighted-degree hypothesis, so
there is no caller-supplied denominator estimate. -/
theorem integralBranchIteratedWeight_regularizedBranchEvaluation_le
    {K : Type*} [Field K] (factor polynomial : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0)
    (outerDegree ell factorBound polynomialBound : Nat)
    (degreeLe : polynomial.natDegree ≤ outerDegree)
    (factorCoefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ factorBound)
    (polynomialCoefficientBound : ∀ exponent ∈ polynomial.support,
      (polynomial.coeff exponent).natDegree + ell * exponent ≤
        polynomialBound) :
    integralBranchIteratedWeight factor factorNeZero
        (factorBound + ell - ell * factor.natDegree)
        (regularizedBranchEvaluation factor polynomial outerDegree) ≤
      polynomialBound + outerDegree *
        (factorBound - ell * factor.natDegree) := by
  let wBound := factorBound - ell * factor.natDegree
  have leadingMem : factor.natDegree ∈ factor.support :=
    Polynomial.natDegree_mem_support_of_nonzero factorNeZero
  have leadingBound := factorCoefficientBound factor.natDegree leadingMem
  have degreeWeightLe : ell * factor.natDegree ≤ factorBound := by
    omega
  have leadingDegree : factor.leadingCoeff.natDegree ≤ wBound := by
    change factor.leadingCoeff.natDegree + ell * factor.natDegree ≤
      factorBound at leadingBound
    dsimp [wBound]
    omega
  have generatorWeight :
      factorBound + ell - ell * factor.natDegree = wBound + ell := by
    dsimp [wBound]
    omega
  have quotientRepresentation :
      regularizedBranchEvaluation factor polynomial outerDegree =
        AdjoinRoot.mk (integralLocalFactor factor)
          (C (factor.leadingCoeff ^
              (outerDegree - polynomial.natDegree)) *
            polynomial.scaleRoots factor.leadingCoeff) := by
    unfold regularizedBranchEvaluation AdjoinRoot.of
    change AdjoinRoot.mk (integralLocalFactor factor)
        (C (factor.leadingCoeff ^ (outerDegree - polynomial.natDegree))) *
      AdjoinRoot.mk (integralLocalFactor factor)
        (polynomial.scaleRoots factor.leadingCoeff) = _
    exact ((AdjoinRoot.mk (integralLocalFactor factor)).map_mul _ _).symm
  let rawRepresentative :=
    C (factor.leadingCoeff ^ (outerDegree - polynomial.natDegree)) *
      polynomial.scaleRoots factor.leadingCoeff
  calc
    integralBranchIteratedWeight factor factorNeZero
        (factorBound + ell - ell * factor.natDegree)
        (regularizedBranchEvaluation factor polynomial outerDegree) =
      integralBranchIteratedWeight factor factorNeZero (wBound + ell)
        (AdjoinRoot.mk (integralLocalFactor factor) rawRepresentative) := by
          rw [quotientRepresentation, generatorWeight]
    _ ≤ iteratedBivariateWeight (wBound + ell) rawRepresentative := by
      have bounded := integralBranchIteratedWeight_mk_le factor factorNeZero
        ell factorBound factorCoefficientBound rawRepresentative
      rw [generatorWeight] at bounded
      exact bounded
    _ ≤ polynomialBound + outerDegree * wBound :=
      regularizedPolynomial_iteratedWeight_le polynomial factor.leadingCoeff
        outerDegree ell polynomialBound wBound degreeLe leadingDegree
        polynomialCoefficientBound

#print axioms integralBranchToFunctionField_regularizedBranchEvaluation
#print axioms integralBranchSpecialization_regularizedBranchEvaluation_eq_zero
#print axioms integralBranchSpecialization_regularizedBranchEvaluation
#print axioms regularizedPolynomial_iteratedWeight_le
#print axioms integralBranchIteratedWeight_regularizedBranchEvaluation_le

end

end AspisK1.V7ExactCorrelatedAgreementRegularEvaluation
