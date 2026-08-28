import AspisFormal.K1.V7ExactCorrelatedAgreementLocalFactors
import Mathlib.RingTheory.AdjoinRoot

/-!
# The fixed local branch as an algebraic function field

For a fixed irreducible local factor `H(Y,Z)` of `R(x₀,Y,Z)`, this module
constructs the literal finite extension `QM31(Z)[Y]/(H)`.  It proves that the
adjoined root is a root of the parent and that it is simple there.  The latter
is derived from the nonzero resultant certificate chosen before
specialization, so no characteristic-zero or degree-preservation shortcut is
used.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementFunctionField

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The exact rational function field in the batching challenge. -/
abbrev ChallengeRationalField (K : Type*) [Field K] :=
  FractionRing (Polynomial K)

/-- A local bivariate factor, regarded as a polynomial in `Y` over `K(Z)`. -/
def localFactorOverRational
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    Polynomial (ChallengeRationalField K) :=
  factor.map (algebraMap (Polynomial K) (ChallengeRationalField K))

/-- A fixed prime local branch remains irreducible after extending the
coefficient ring from `K[Z]` to `K(Z)`. -/
theorem localFactorOverRational_irreducible
    {K : Type*} [Field K]
    (parent factor : BivariatePolynomial K)
    (parentNeZero : parent ≠ 0)
    (factorMem : factor ∈ bivariatePrimeFactors parent)
    (factorPositive : 0 < factor.natDegree) :
    Irreducible (localFactorOverRational factor) := by
  have factorIrreducible : Irreducible factor :=
    (bivariatePrimeFactors_prime parent parentNeZero factor factorMem).irreducible
  have factorPrimitive : factor.IsPrimitive :=
    factorIrreducible.isPrimitive (Nat.ne_of_gt factorPositive)
  exact (factorPrimitive.irreducible_iff_irreducible_map_fraction_map).mp
    factorIrreducible

/-- The concrete algebraic function field cut out by the fixed local branch. -/
abbrev LocalBranchField
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :=
  AdjoinRoot (localFactorOverRational factor)

/-- Every positive natural below the M31 characteristic is nonzero already in
the coefficient ring `QM31[Z]`. -/
theorem bivariateCoefficient_natCast_ne_zero_of_pos_of_lt_characteristic
    (degree : Nat) (degreePositive : 0 < degree) (degreeSmall : degree < P) :
    (degree : Polynomial QM31Exact) ≠ 0 := by
  have baseNonzero :=
    qm31Exact_natCast_ne_zero_of_pos_of_lt_characteristic degree
      degreePositive degreeSmall
  intro polynomialZero
  apply baseNonzero
  have constantCoefficientZero := congrArg
    (fun coefficient : Polynomial QM31Exact => coefficient.coeff 0)
    polynomialZero
  simpa using constantCoefficientZero

/-- Exact finite-characteristic separability of every local branch that can
occur in the V7 interpolant. -/
theorem exactV7_localPrimeFactor_derivative_ne_zero
    (globalPolynomial globalFactor : TrivariatePolynomial QM31Exact)
    (globalPolynomialNeZero : globalPolynomial ≠ 0)
    (globalFactorMem : globalFactor ∈ curvePrimeFactors globalPolynomial)
    (globalPolynomialDegreeSmall : globalPolynomial.natDegree < 113)
    (x : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    (localFactorMem : localFactor ∈
      bivariatePrimeFactors (specializeEvaluationPoint x globalFactor))
    (localFactorPositive : 0 < localFactor.natDegree) :
    localFactor.derivative ≠ 0 := by
  have globalFactorDegreeLe : globalFactor.natDegree ≤
      globalPolynomial.natDegree :=
    curvePrimeFactor_natDegree_le globalPolynomial globalFactor
      globalPolynomialNeZero globalFactorMem
  have localFactorDvd : localFactor ∣ specializeEvaluationPoint x globalFactor :=
    (Multiset.dvd_prod localFactorMem).trans
      (bivariatePrimeFactors_product_associated
        (specializeEvaluationPoint x globalFactor) (by
          intro specializedZero
          have noFactor : bivariatePrimeFactors
              (specializeEvaluationPoint x globalFactor) = 0 := by
            simp [bivariatePrimeFactors, specializedZero]
          rw [noFactor] at localFactorMem
          simpa using localFactorMem)).dvd
  have localFactorDegreeLe : localFactor.natDegree ≤ globalFactor.natDegree :=
    (Polynomial.natDegree_le_of_dvd localFactorDvd (by
      intro specializedZero
      have noFactor : bivariatePrimeFactors
          (specializeEvaluationPoint x globalFactor) = 0 := by
        simp [bivariatePrimeFactors, specializedZero]
      rw [noFactor] at localFactorMem
      simpa using localFactorMem)).trans Polynomial.natDegree_map_le
  have degreeSmall : localFactor.natDegree < P :=
    localFactorDegreeLe.trans_lt <| globalFactorDegreeLe.trans_lt <|
      globalPolynomialDegreeSmall.trans <| by norm_num [P]
  exact derivative_ne_zero_of_natDegree_pos_of_cast_ne_zero localFactor
    localFactorPositive
    (bivariateCoefficient_natCast_ne_zero_of_pos_of_lt_characteristic
      localFactor.natDegree localFactorPositive degreeSmall)

/-- Mapping a local branch to the rational function field preserves its
positive degree exactly. -/
theorem localFactorOverRational_natDegree
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    (localFactorOverRational factor).natDegree = factor.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective (Polynomial K) (ChallengeRationalField K)) factor

/-- The adjoined branch root is a root of the whole specialized parent. -/
theorem localBranchRoot_isRoot_parent
    {K : Type*} [Field K]
    (parent factor : BivariatePolynomial K)
    (parentNeZero : parent ≠ 0)
    (factorMem : factor ∈ bivariatePrimeFactors parent)
    (factorPositive : 0 < factor.natDegree) :
    letI : Fact (Irreducible (localFactorOverRational factor)) :=
      ⟨localFactorOverRational_irreducible parent factor parentNeZero
        factorMem factorPositive⟩
    (parent.map (algebraMap (Polynomial K) (ChallengeRationalField K))).map
        (AdjoinRoot.of (localFactorOverRational factor)) |>.IsRoot
      (AdjoinRoot.root (localFactorOverRational factor)) := by
  letI : Fact (Irreducible (localFactorOverRational factor)) :=
    ⟨localFactorOverRational_irreducible parent factor parentNeZero
      factorMem factorPositive⟩
  have factorDvdParent : factor ∣ parent :=
    (Multiset.dvd_prod factorMem).trans
      (bivariatePrimeFactors_product_associated parent parentNeZero).dvd
  have mappedDvd :
      (localFactorOverRational factor).map
          (AdjoinRoot.of (localFactorOverRational factor)) ∣
        (parent.map
          (algebraMap (Polynomial K) (ChallengeRationalField K))).map
          (AdjoinRoot.of (localFactorOverRational factor)) := by
    have firstMap : localFactorOverRational factor ∣
        parent.map
          (algebraMap (Polynomial K) (ChallengeRationalField K)) := by
      exact Polynomial.map_dvd _ factorDvdParent
    exact Polynomial.map_dvd _ firstMap
  exact (AdjoinRoot.isRoot_root
    (localFactorOverRational factor)).dvd mappedDvd

/-- The fixed local branch root is simple for its whole specialized parent.
This is the exact Hensel side condition: ordinary divisibility alone is not
used.  A hypothetical derivative root would kill the bounded Sylvester
resultant after two injective field embeddings. -/
theorem localBranchRoot_not_isRoot_parentDerivative
    (globalFactor : TrivariatePolynomial QM31Exact)
    (x : QM31Exact)
    (certificateAtPoint :
      (Polynomial.Bivariate.swap
        (separabilityCertificate globalFactor)).eval (C x) ≠ 0)
    (localFactor : BivariatePolynomial QM31Exact)
    (localFactorMem : localFactor ∈
      bivariatePrimeFactors (specializeEvaluationPoint x globalFactor))
    (localFactorPositive : 0 < localFactor.natDegree) :
    letI : Fact (Irreducible (localFactorOverRational localFactor)) :=
      ⟨localFactorOverRational_irreducible
        (specializeEvaluationPoint x globalFactor) localFactor (by
          intro parentZero
          have noFactor : bivariatePrimeFactors
              (specializeEvaluationPoint x globalFactor) = 0 := by
            simp [bivariatePrimeFactors, parentZero]
          rw [noFactor] at localFactorMem
          simpa using localFactorMem)
        localFactorMem localFactorPositive⟩
    ¬((((specializeEvaluationPoint x globalFactor).derivative).map
        (algebraMap (Polynomial QM31Exact)
          (ChallengeRationalField QM31Exact))).map
        (AdjoinRoot.of (localFactorOverRational localFactor))).IsRoot
      (AdjoinRoot.root (localFactorOverRational localFactor)) := by
  let parent := specializeEvaluationPoint x globalFactor
  have parentNeZero : parent ≠ 0 := by
    intro parentZero
    have noFactor : bivariatePrimeFactors parent = 0 := by
      simp [bivariatePrimeFactors, parentZero]
    rw [noFactor] at localFactorMem
    simpa using localFactorMem
  letI : Fact (Irreducible (localFactorOverRational localFactor)) :=
    ⟨localFactorOverRational_irreducible parent localFactor parentNeZero
      localFactorMem localFactorPositive⟩
  intro derivativeRoot
  have parentRoot := localBranchRoot_isRoot_parent parent localFactor
    parentNeZero localFactorMem localFactorPositive
  let rationalMap : Polynomial QM31Exact →+*
      ChallengeRationalField QM31Exact :=
    algebraMap (Polynomial QM31Exact) (ChallengeRationalField QM31Exact)
  let branchMap : ChallengeRationalField QM31Exact →+*
      LocalBranchField localFactor :=
    AdjoinRoot.of (localFactorOverRational localFactor)
  have resultantZero : Polynomial.resultant
      (parent.map rationalMap |>.map branchMap)
      (parent.derivative.map rationalMap |>.map branchMap)
      globalFactor.natDegree globalFactor.derivative.natDegree = 0 := by
    have parentDegreePositive : 0 < parent.natDegree :=
      lt_of_lt_of_le localFactorPositive <|
        Polynomial.natDegree_le_of_dvd
          ((Multiset.dvd_prod localFactorMem).trans
            (bivariatePrimeFactors_product_associated parent parentNeZero).dvd)
          parentNeZero
    have globalDegreePositive : 0 < globalFactor.natDegree :=
      parentDegreePositive.trans_le Polynomial.natDegree_map_le
    have leftDegreeLe :
        (parent.map rationalMap |>.map branchMap).natDegree ≤
          globalFactor.natDegree :=
      (Polynomial.natDegree_map_le.trans
        Polynomial.natDegree_map_le).trans Polynomial.natDegree_map_le
    have specializeDerivative :
        specializeEvaluationPoint x globalFactor.derivative =
          parent.derivative := by
      change globalFactor.derivative.map (evaluateInnerVariable x) =
        (globalFactor.map (evaluateInnerVariable x)).derivative
      rw [Polynomial.derivative_map]
    have rightDegreeLe :
        (parent.derivative.map rationalMap |>.map branchMap).natDegree ≤
          globalFactor.derivative.natDegree := by
      calc
        (parent.derivative.map rationalMap |>.map branchMap).natDegree ≤
            parent.derivative.natDegree :=
          Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le
        _ = (specializeEvaluationPoint x
              globalFactor.derivative).natDegree := by rw [specializeDerivative]
        _ ≤ globalFactor.derivative.natDegree := Polynomial.natDegree_map_le
    exact resultant_eq_zero_of_common_root_of_natDegree_le
      _ _ _ _ (AdjoinRoot.root (localFactorOverRational localFactor))
      globalDegreePositive leftDegreeLe rightDegreeLe parentRoot derivativeRoot
  have mappedCertificateZero : branchMap
      (rationalMap ((Polynomial.Bivariate.swap
        (separabilityCertificate globalFactor)).eval (C x))) = 0 := by
    rw [← specialized_resultant_eq_certificate_eval_x globalFactor x]
    have specializeDerivative :
        specializeEvaluationPoint x globalFactor.derivative =
          parent.derivative := by
      change globalFactor.derivative.map (evaluateInnerVariable x) =
        (globalFactor.map (evaluateInnerVariable x)).derivative
      rw [Polynomial.derivative_map]
    calc
      branchMap (rationalMap (Polynomial.resultant parent
          (specializeEvaluationPoint x globalFactor.derivative)
          globalFactor.natDegree globalFactor.derivative.natDegree)) =
          branchMap (Polynomial.resultant (parent.map rationalMap)
            ((specializeEvaluationPoint x globalFactor.derivative).map
              rationalMap)
            globalFactor.natDegree globalFactor.derivative.natDegree) :=
        congrArg branchMap (Polynomial.resultant_map_map parent
          (specializeEvaluationPoint x globalFactor.derivative)
          globalFactor.natDegree globalFactor.derivative.natDegree
          rationalMap).symm
      _ = Polynomial.resultant
          ((parent.map rationalMap).map branchMap)
          (((specializeEvaluationPoint x globalFactor.derivative).map
            rationalMap).map branchMap)
          globalFactor.natDegree globalFactor.derivative.natDegree :=
        (Polynomial.resultant_map_map (parent.map rationalMap)
          ((specializeEvaluationPoint x globalFactor.derivative).map
            rationalMap)
          globalFactor.natDegree globalFactor.derivative.natDegree
          branchMap).symm
      _ = Polynomial.resultant
          ((parent.map rationalMap).map branchMap)
          (((parent.derivative).map rationalMap).map branchMap)
          globalFactor.natDegree globalFactor.derivative.natDegree := by
        rw [specializeDerivative]
      _ = 0 := resultantZero
  have rationalCertificateZero : rationalMap
      ((Polynomial.Bivariate.swap
        (separabilityCertificate globalFactor)).eval (C x)) = 0 :=
    (AdjoinRoot.of (localFactorOverRational localFactor)).injective <| by
      simpa only [map_zero] using mappedCertificateZero
  exact certificateAtPoint
    ((IsFractionRing.injective (Polynomial QM31Exact)
      (ChallengeRationalField QM31Exact)) <| by
        simpa only [map_zero] using rationalCertificateZero)

#print axioms localFactorOverRational_irreducible
#print axioms exactV7_localPrimeFactor_derivative_ne_zero
#print axioms localBranchRoot_isRoot_parent
#print axioms localBranchRoot_not_isRoot_parentDerivative

end

end AspisK1.V7ExactCorrelatedAgreementFunctionField
