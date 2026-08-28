import AspisFormal.K1.V7ExactCorrelatedAgreementRegularHensel

/-!
# The regular Hensel denominator `xi`

BCIKS uses `xi = W^(d-2) * dR/dY(x0,T/W,Z)`, not the easier
`W^(d-1)` multiple.  The top derivative coefficient is regular only because
the fixed local factor's leading coefficient `W` divides the leading
coefficient of its actual parent.  This module constructs that exact element
and proves its function-field identity without division.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementRegularXi

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementRegularEvaluation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The derivative with its unique possible coefficient in degree `d-1`
removed. -/
def derivativeBelowLeading
    {K : Type*} [Field K] (parent : BivariatePolynomial K) :
    BivariatePolynomial K :=
  parent.derivative.erase (parent.natDegree - 1)

/-- Removing the `d-1` coefficient leaves degree at most `d-2`. -/
theorem derivativeBelowLeading_natDegree_le
    {K : Type*} [Field K] (parent : BivariatePolynomial K)
    (degreeAtLeastTwo : 2 ≤ parent.natDegree) :
    (derivativeBelowLeading parent).natDegree ≤ parent.natDegree - 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro exponent exponentLarge
  unfold derivativeBelowLeading
  by_cases top : exponent = parent.natDegree - 1
  · subst exponent
    simp
  · rw [Polynomial.coeff_erase]
    simp only [top, if_false]
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mp
      (Polynomial.natDegree_derivative_le parent)
    omega

/-- The exact derivative decomposition used in the regularity proof. -/
theorem derivative_eq_leading_add_below
    {K : Type*} [Field K] (parent : BivariatePolynomial K)
    (parentNeZero : parent ≠ 0) (degreePositive : 0 < parent.natDegree) :
    parent.derivative =
      Polynomial.monomial (parent.natDegree - 1)
          ((parent.natDegree : Polynomial K) * parent.leadingCoeff) +
        derivativeBelowLeading parent := by
  have successor : parent.natDegree - 1 + 1 = parent.natDegree := by omega
  have castSuccessor :
      ((parent.natDegree - 1 : Nat) : Polynomial K) + 1 =
        (parent.natDegree : Polynomial K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun value : Nat => (value : Polynomial K)) successor
  have topCoefficient : parent.derivative.coeff (parent.natDegree - 1) =
      (parent.natDegree : Polynomial K) * parent.leadingCoeff := by
    rw [Polynomial.coeff_derivative, successor, castSuccessor]
    change parent.leadingCoeff * (parent.natDegree : Polynomial K) = _
    ring
  symm
  calc
    Polynomial.monomial (parent.natDegree - 1)
          ((parent.natDegree : Polynomial K) * parent.leadingCoeff) +
        derivativeBelowLeading parent =
      Polynomial.monomial (parent.natDegree - 1)
          (parent.derivative.coeff (parent.natDegree - 1)) +
        parent.derivative.erase (parent.natDegree - 1) := by
          rw [topCoefficient]
          rfl
    _ = parent.derivative :=
      parent.derivative.monomial_add_erase (parent.natDegree - 1)

/-- A division-free representative of
`xi = W^(d-2) * dR/dY(x0,T/W,Z)` in the actual integral local quotient.
`leadingQuotient` is subsequently obtained from the fixed factorization. -/
def regularizedHenselXi
    {K : Type*} [Field K]
    (localFactor parent : BivariatePolynomial K)
    (leadingQuotient : Polynomial K) : IntegralLocalBranch localFactor :=
  regularizedBranchEvaluation localFactor
      (derivativeBelowLeading parent) (parent.natDegree - 2) +
    AdjoinRoot.of (integralLocalFactor localFactor)
        ((parent.natDegree : Polynomial K) * leadingQuotient) *
      AdjoinRoot.root (integralLocalFactor localFactor) ^
        (parent.natDegree - 1)

/-- Exact function-field identity for `xi`.  The proof uses the literal
leading-coefficient quotient `parent.leadingCoeff = W * quotient`; no inverse
of `W` is introduced. -/
theorem integralBranchToFunctionField_regularizedHenselXi
    {K : Type*} [Field K]
    (localFactor parent : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (parentNeZero : parent ≠ 0)
    (degreeAtLeastTwo : 2 ≤ parent.natDegree)
    (leadingQuotient : Polynomial K)
    (leadingEquation :
      localFactor.leadingCoeff * leadingQuotient = parent.leadingCoeff) :
    integralBranchToFunctionField localFactor
        (regularizedHenselXi localFactor parent leadingQuotient) =
      regularCoefficientMap localFactor localFactor.leadingCoeff ^
          (parent.natDegree - 2) *
        parent.derivative.eval₂ (regularCoefficientMap localFactor)
          (AdjoinRoot.root (localFactorOverRational localFactor)) := by
  let coefficientMap := regularCoefficientMap localFactor
  let branchRoot := AdjoinRoot.root (localFactorOverRational localFactor)
  have lowerDegree := derivativeBelowLeading_natDegree_le parent
    degreeAtLeastTwo
  have derivativeDecomposition := derivative_eq_leading_add_below parent
    parentNeZero (by omega)
  have mappedLeading : coefficientMap parent.leadingCoeff =
      coefficientMap localFactor.leadingCoeff *
        coefficientMap leadingQuotient := by
    rw [← leadingEquation, map_mul]
  rw [regularizedHenselXi, map_add, map_mul, map_pow,
    integralBranchToFunctionField_regularizedBranchEvaluation localFactor
      (derivativeBelowLeading parent) (parent.natDegree - 2) lowerDegree,
    integralBranchToFunctionField_of,
    integralBranchToFunctionField_root]
  change coefficientMap localFactor.leadingCoeff ^ (parent.natDegree - 2) *
        (derivativeBelowLeading parent).eval₂ coefficientMap branchRoot +
      coefficientMap
          ((parent.natDegree : Polynomial K) * leadingQuotient) *
        (coefficientMap localFactor.leadingCoeff * branchRoot) ^
          (parent.natDegree - 1) = _
  rw [derivativeDecomposition, Polynomial.eval₂_add,
    Polynomial.eval₂_monomial]
  simp only [map_mul, map_natCast]
  rw [mappedLeading]
  have exponentIdentity :
      parent.natDegree - 2 + 1 = parent.natDegree - 1 := by omega
  rw [mul_pow]
  have powerIdentity :
      coefficientMap localFactor.leadingCoeff ^ (parent.natDegree - 1) =
        coefficientMap localFactor.leadingCoeff ^ (parent.natDegree - 2) *
          coefficientMap localFactor.leadingCoeff := by
    rw [← exponentIdentity, pow_succ]
  rw [powerIdentity]
  ring

/-- For the exact fixed local branch, the required leading quotient and the
regular `xi` are produced from the existing prime-factor membership.  The
result exposes only concrete algebraic data, not an assumed regularity
predicate. -/
theorem exists_exactV7_regularizedHenselXi
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    (localFactorMem : localFactor ∈
      bivariatePrimeFactors (specializeEvaluationPoint x₀ globalFactor))
    (localFactorPositive : 0 < localFactor.natDegree)
    (parentDegreeAtLeastTwo :
      2 ≤ (specializeEvaluationPoint x₀ globalFactor).natDegree) :
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
    ∃ xi : IntegralLocalBranch localFactor,
      integralBranchToFunctionField localFactor xi =
        regularCoefficientMap localFactor localFactor.leadingCoeff ^
            (parent.natDegree - 2) *
          parent.derivative.eval₂ (regularCoefficientMap localFactor)
            (AdjoinRoot.root (localFactorOverRational localFactor)) := by
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
  obtain ⟨leadingQuotient, _leadingQuotientNeZero, leadingEquation⟩ :=
    exists_leadingCoeff_quotient_of_bivariatePrimeFactor parent localFactor
      parentNeZero localFactorMem
  refine ⟨regularizedHenselXi localFactor parent leadingQuotient, ?_⟩
  exact integralBranchToFunctionField_regularizedHenselXi localFactor parent
    parentNeZero parentDegreeAtLeastTwo leadingQuotient leadingEquation

/-- The exact regular `xi` is nonzero in finite characteristic.  Nonvanishing
comes from the previously proved resultant/separability certificate for the
fixed branch and injectivity of the coefficient embedding. -/
theorem exists_exactV7_regularizedHenselXi_ne_zero
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (certificateAtPoint :
      (Polynomial.Bivariate.swap
        (separabilityCertificate globalFactor)).eval (C x₀) ≠ 0)
    (localFactor : BivariatePolynomial QM31Exact)
    (localFactorMem : localFactor ∈
      bivariatePrimeFactors (specializeEvaluationPoint x₀ globalFactor))
    (localFactorPositive : 0 < localFactor.natDegree)
    (parentDegreeAtLeastTwo :
      2 ≤ (specializeEvaluationPoint x₀ globalFactor).natDegree) :
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
    ∃ xi : IntegralLocalBranch localFactor,
      xi ≠ 0 ∧
        integralBranchToFunctionField localFactor xi =
          regularCoefficientMap localFactor localFactor.leadingCoeff ^
              (parent.natDegree - 2) *
            parent.derivative.eval₂ (regularCoefficientMap localFactor)
              (AdjoinRoot.root (localFactorOverRational localFactor)) := by
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
  obtain ⟨leadingQuotient, _leadingQuotientNeZero, leadingEquation⟩ :=
    exists_leadingCoeff_quotient_of_bivariatePrimeFactor parent localFactor
      parentNeZero localFactorMem
  let xi := regularizedHenselXi localFactor parent leadingQuotient
  have xiImage :=
    integralBranchToFunctionField_regularizedHenselXi localFactor parent
      parentNeZero parentDegreeAtLeastTwo leadingQuotient leadingEquation
  have localFactorNeZero : localFactor ≠ 0 :=
    (bivariatePrimeFactors_prime parent parentNeZero localFactor
      localFactorMem).ne_zero
  have leadingNeZero : localFactor.leadingCoeff ≠ 0 :=
    mt Polynomial.leadingCoeff_eq_zero.mp localFactorNeZero
  have mappedLeadingNeZero :
      regularCoefficientMap localFactor localFactor.leadingCoeff ≠ 0 := by
    simpa only [map_zero] using
      (regularCoefficientMap_injective localFactor).ne leadingNeZero
  have derivativeValueNeZero :
      parent.derivative.eval₂ (regularCoefficientMap localFactor)
          (AdjoinRoot.root (localFactorOverRational localFactor)) ≠ 0 := by
    rw [Polynomial.eval₂_eq_eval_map]
    simpa [Polynomial.IsRoot, regularCoefficientMap, Polynomial.map_map,
      parent] using
      (localBranchRoot_not_isRoot_parentDerivative globalFactor x₀
        certificateAtPoint localFactor localFactorMem localFactorPositive)
  have imageNeZero : integralBranchToFunctionField localFactor xi ≠ 0 := by
    rw [xiImage]
    exact mul_ne_zero (pow_ne_zero _ mappedLeadingNeZero)
      derivativeValueNeZero
  refine ⟨xi, ?_, xiImage⟩
  intro xiZero
  apply imageNeZero
  rw [xiZero, map_zero]

#print axioms derivativeBelowLeading_natDegree_le
#print axioms derivative_eq_leading_add_below
#print axioms integralBranchToFunctionField_regularizedHenselXi
#print axioms exists_exactV7_regularizedHenselXi
#print axioms exists_exactV7_regularizedHenselXi_ne_zero

end

end AspisK1.V7ExactCorrelatedAgreementRegularXi
