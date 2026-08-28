import AspisFormal.K1.V7ExactCorrelatedAgreementFactors
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Smooth-specialization boundary for exact V7 correlated agreement

This file isolates the separability conditions used before Hensel extraction.
The outer variable of the trivariate interpolant is `Y`; its coefficient ring
is `K[X,Z]`.  A fixed irreducible branch has a nonzero `Y`-derivative by the
explicit QM31 characteristic calculation in the factor module.  Its
`Y`-resultant with that derivative is then a literal nonzero polynomial in
`X,Z`, whose specializations control collisions and root multiplicities.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementSmooth

open scoped BigOperators Polynomial.Bivariate
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Reorder `K[X,Z,Y]` so that `X` is the outer variable.  The first swap
exchanges `X` and `Z` inside every `Y` coefficient; the second exchanges that
new outer `X` with `Y`. -/
noncomputable def trivariateXOuterEquiv (K : Type*) [Field K] :
    TrivariatePolynomial K ≃ₐ[K]
      Polynomial (Polynomial (Polynomial K)) :=
  (Polynomial.mapAlgEquiv (Polynomial.Bivariate.swap (R := K))).trans
    ((Polynomial.Bivariate.swap (R := Polynomial K)).restrictScalars K)

theorem trivariateXOuterEquiv_monomial
    {K : Type*} [Field K] (yExponent zExponent xExponent : Nat) (value : K) :
    trivariateXOuterEquiv K
        (Polynomial.monomial yExponent
          (Polynomial.monomial zExponent
            (Polynomial.monomial xExponent value))) =
      Polynomial.monomial xExponent
        (Polynomial.monomial yExponent
          (Polynomial.monomial zExponent value)) := by
  change Polynomial.Bivariate.swap
      (Polynomial.map (Polynomial.Bivariate.swap (R := K)).toRingHom
        (Polynomial.monomial yExponent
          (Polynomial.monomial zExponent
            (Polynomial.monomial xExponent value)))) = _
  rw [Polynomial.map_monomial]
  change Polynomial.Bivariate.swap
      (Polynomial.monomial yExponent
        (Polynomial.Bivariate.swap
          (Polynomial.monomial zExponent
            (Polynomial.monomial xExponent value)))) = _
  rw [Polynomial.Bivariate.swap_monomial_monomial,
    Polynomial.Bivariate.swap_monomial_monomial]

/-- Swapping a bivariate polynomial literally transposes its coefficient
matrix. -/
theorem coeff_coeff_bivariate_swap
    {R : Type*} [CommRing R] (polynomial : Polynomial (Polynomial R))
    (outer inner : Nat) :
    ((Polynomial.Bivariate.swap polynomial).coeff inner).coeff outer =
      (polynomial.coeff outer).coeff inner := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp only [map_add, Polynomial.coeff_add, leftInduction, rightInduction]
  | monomial outerExponent coefficient =>
      rw [Polynomial.Bivariate.swap_monomial]
      rw [Polynomial.coeff_mul_C, Polynomial.coeff_map,
        Polynomial.coeff_C_mul_X_pow]
      by_cases same : outer = outerExponent
      · simp [same]
      · have opposite : outerExponent ≠ outer := Ne.symm same
        simp [Polynomial.coeff_monomial, same, opposite]

/-- Consequently each original coefficient's `X` degree is bounded by the
outer degree of the swapped polynomial. -/
theorem coeff_natDegree_le_bivariate_swap_natDegree
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (polynomial : Polynomial (Polynomial R)) (coefficient : Nat) :
    (polynomial.coeff coefficient).natDegree ≤
      (Polynomial.Bivariate.swap polynomial).natDegree := by
  by_cases coefficientZero : polynomial.coeff coefficient = 0
  · simp [coefficientZero]
  apply Polynomial.le_natDegree_of_ne_zero
  intro swappedCoefficientZero
  have entryZero := congrArg
    (fun value : Polynomial R => value.coeff coefficient)
    swappedCoefficientZero
  rw [coeff_coeff_bivariate_swap] at entryZero
  exact (Polynomial.leadingCoeff_ne_zero.mpr coefficientZero) entryZero

/-- The exact finite coefficient representation also records a strict bound
on the genuine `X` degree after variables are reordered. -/
theorem curveTrivariatePolynomial_xNatDegree_lt
    {K : Type*} [Field K]
    {maximumDegree curveDegree xBound yRows zBound : Nat}
    (xBoundPositive : 0 < xBound)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) :
    (trivariateXOuterEquiv K
      (curveTrivariatePolynomial coefficients)).natDegree < xBound := by
  classical
  refine lt_of_le_of_lt (b := xBound - 1) ?_ (by omega)
  unfold curveTrivariatePolynomial
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro monomial _
  rw [trivariateXOuterEquiv_monomial]
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- A fixed global factor cannot have larger `X` degree than its parent
interpolant. -/
theorem curvePrimeFactor_xNatDegree_le
    {K : Type*} [Field K]
    (polynomial factor : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial) :
    (trivariateXOuterEquiv K factor).natDegree ≤
      (trivariateXOuterEquiv K polynomial).natDegree := by
  have associatedProduct :=
    curvePrimeFactors_product_associated polynomial polynomialNeZero
  have factorDvd : factor ∣ polynomial :=
    (Multiset.dvd_prod factorMem).trans associatedProduct.dvd
  have mappedDvd := _root_.map_dvd (trivariateXOuterEquiv K).toRingHom factorDvd
  exact Polynomial.natDegree_le_of_dvd mappedDvd
    (by simpa using
      (trivariateXOuterEquiv K).injective.ne polynomialNeZero)

/-- The coefficient-field fraction ring used only to prove that the
resultant certificate is nonzero. -/
abbrev CoefficientFractionField (K : Type*) [Field K] :=
  FractionRing (Polynomial (Polynomial K))

/-- A prime positive-`Y` factor with nonzero derivative has a nonzero
resultant with its derivative.  The proof passes through the fraction field
and Gauss's lemma; no Bézout property is incorrectly assumed for `K[X,Z]`. -/
theorem curvePrimeFactor_resultant_derivative_ne_zero
    {K : Type*} [Field K]
    (polynomial factor : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial)
    (factorPositive : 0 < factor.natDegree)
    (derivativeNeZero : factor.derivative ≠ 0) :
    Polynomial.resultant factor factor.derivative ≠ 0 := by
  let coefficientMap : Polynomial (Polynomial K) →+*
      CoefficientFractionField K :=
    algebraMap (Polynomial (Polynomial K)) (CoefficientFractionField K)
  have coefficientMapInjective : Function.Injective coefficientMap :=
    IsFractionRing.injective _ _
  have factorIrreducible : Irreducible factor :=
    (curvePrimeFactors_prime polynomial polynomialNeZero factor factorMem).irreducible
  have factorPrimitive : factor.IsPrimitive :=
    factorIrreducible.isPrimitive (Nat.ne_of_gt factorPositive)
  have mappedIrreducible : Irreducible (factor.map coefficientMap) :=
    (factorPrimitive.irreducible_iff_irreducible_map_fraction_map).mp
      factorIrreducible
  have mappedDerivativeNeZero : (factor.map coefficientMap).derivative ≠ 0 := by
    rw [Polynomial.derivative_map]
    simpa using
      (Polynomial.map_injective coefficientMap coefficientMapInjective).ne
        derivativeNeZero
  have mappedSeparable : (factor.map coefficientMap).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero mappedIrreducible).mpr
      mappedDerivativeNeZero
  have mappedResultantNeZero : Polynomial.resultant
      (factor.map coefficientMap) ((factor.derivative).map coefficientMap)
        factor.natDegree factor.derivative.natDegree ≠ 0 := by
    have degreeFactor : (factor.map coefficientMap).natDegree = factor.natDegree :=
      Polynomial.natDegree_map_eq_of_injective coefficientMapInjective factor
    have degreeDerivative :
        ((factor.derivative).map coefficientMap).natDegree =
          factor.derivative.natDegree :=
      Polynomial.natDegree_map_eq_of_injective coefficientMapInjective
        factor.derivative
    rw [← degreeFactor, ← degreeDerivative, ← Polynomial.derivative_map]
    exact Polynomial.resultant_ne_zero _ _
      ((Polynomial.separable_def _).mp mappedSeparable)
  intro resultantZero
  apply mappedResultantNeZero
  rw [Polynomial.resultant_map_map]
  rw [resultantZero, map_zero]

/-- The literal collision/multiplicity certificate for a fixed branch.  Its
nonvanishing after specialization is what licenses a simple-root lift. -/
def separabilityCertificate
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) :
    Polynomial (Polynomial K) :=
  Polynomial.resultant factor factor.derivative factor.natDegree
    factor.derivative.natDegree

theorem separabilityCertificate_ne_zero
    {K : Type*} [Field K]
    (polynomial factor : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial)
    (factorPositive : 0 < factor.natDegree)
    (derivativeNeZero : factor.derivative ≠ 0) :
    separabilityCertificate factor ≠ 0 :=
  curvePrimeFactor_resultant_derivative_ne_zero polynomial factor
    polynomialNeZero factorMem factorPositive derivativeNeZero

private theorem matrix_det_natDegree_le
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι R[X]) (bound : Nat)
    (entries : ∀ row column, (matrix row column).natDegree ≤ bound) :
    matrix.det.natDegree ≤ Fintype.card ι * bound := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro permutation
  calc
    (Equiv.Perm.sign permutation •
        ∏ index : ι, matrix (permutation index) index).natDegree ≤
        (∏ index : ι, matrix (permutation index) index).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with sign | sign
      · rw [sign, one_smul]
      · rw [sign, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ index : ι,
        (matrix (permutation index) index).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ _
    _ ≤ Finset.univ.card • bound :=
      Finset.sum_le_card_nsmul _ _ bound fun index _ =>
        entries (permutation index) index
    _ = Fintype.card ι * bound := by
      simp [Finset.card_univ]

/-- A determinant-level degree bound for the resultant. -/
theorem resultant_natDegree_le_of_coeff_natDegree_le
    {R : Type*} [CommRing R]
    (left right : Polynomial R[X]) (leftDegree rightDegree bound : Nat)
    (leftCoefficients : ∀ coefficient,
      ((left.coeff coefficient)).natDegree ≤ bound)
    (rightCoefficients : ∀ coefficient,
      ((right.coeff coefficient)).natDegree ≤ bound) :
    (Polynomial.resultant left right leftDegree rightDegree).natDegree ≤
      (leftDegree + rightDegree) * bound := by
  unfold Polynomial.resultant
  have determinantBound := matrix_det_natDegree_le
    (left.sylvester right leftDegree rightDegree) bound (by
      intro row column
      induction column using Fin.addCases with
      | left column =>
          simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
          split_ifs
          · exact rightCoefficients _
          · simp
      | right column =>
          simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
          split_ifs
          · exact leftCoefficients _
          · simp)
  simpa using determinantBound

/-- Reorder only the `X,Z` coefficient variables of an outer-`Y`
polynomial. -/
noncomputable def reorderFactorCoefficients
    (K : Type*) [Field K] (factor : TrivariatePolynomial K) :
    Polynomial (Polynomial (Polynomial K)) :=
  factor.map (Polynomial.Bivariate.swap (R := K)).toRingHom

theorem reorderFactorCoefficients_swap
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) :
    Polynomial.Bivariate.swap (R := Polynomial K)
        (reorderFactorCoefficients K factor) =
      trivariateXOuterEquiv K factor := rfl

theorem reorderFactorCoefficients_coeff_natDegree_le
    {K : Type*} [Field K] (factor : TrivariatePolynomial K)
    (coefficient : Nat) :
    ((reorderFactorCoefficients K factor).coeff coefficient).natDegree ≤
      (trivariateXOuterEquiv K factor).natDegree := by
  rw [← reorderFactorCoefficients_swap]
  exact coeff_natDegree_le_bivariate_swap_natDegree _ coefficient

private theorem bivariate_swap_mul_natCast_natDegree_le
    {K : Type*} [Field K] (polynomial : Polynomial (Polynomial K))
    (scalar : Nat) :
    ((Polynomial.Bivariate.swap (R := K)).toRingHom
      (polynomial * (scalar : Polynomial (Polynomial K)))).natDegree ≤
        ((Polynomial.Bivariate.swap (R := K)).toRingHom polynomial).natDegree := by
  rw [map_mul]
  calc
    ((Polynomial.Bivariate.swap (R := K)).toRingHom polynomial *
      (Polynomial.Bivariate.swap (R := K)).toRingHom
        (scalar : Polynomial (Polynomial K))).natDegree ≤
        ((Polynomial.Bivariate.swap (R := K)).toRingHom polynomial).natDegree +
          ((Polynomial.Bivariate.swap (R := K)).toRingHom
            (scalar : Polynomial (Polynomial K))).natDegree :=
      Polynomial.natDegree_mul_le
    _ = ((Polynomial.Bivariate.swap (R := K)).toRingHom polynomial).natDegree := by
      simp

-- Nested polynomial coercions make this degree calculation elaboration-heavy.
set_option maxHeartbeats 1000000 in
theorem reorderFactorDerivative_coeff_natDegree_le
    {K : Type*} [Field K] (factor : TrivariatePolynomial K)
    (coefficient : Nat) :
    (((factor.derivative).map
        (Polynomial.Bivariate.swap (R := K)).toRingHom).coeff
        coefficient).natDegree ≤
      (trivariateXOuterEquiv K factor).natDegree := by
  rw [Polynomial.coeff_map, Polynomial.coeff_derivative]
  have castSuccessor :
      ((coefficient : Polynomial (Polynomial K)) + 1) =
        ((coefficient + 1 : Nat) : Polynomial (Polynomial K)) := by
    norm_cast
  rw [castSuccessor]
  have coefficientBound :
      ((Polynomial.Bivariate.swap (R := K)).toRingHom
        (factor.coeff (coefficient + 1))).natDegree ≤
          (trivariateXOuterEquiv K factor).natDegree := by
    simpa only [reorderFactorCoefficients, Polynomial.coeff_map] using
      reorderFactorCoefficients_coeff_natDegree_le factor (coefficient + 1)
  exact (bivariate_swap_mul_natCast_natDegree_le
      (factor.coeff (coefficient + 1)) (coefficient + 1)).trans
        coefficientBound

/-- The `X` degree of the resultant certificate is bounded explicitly by
the Sylvester-matrix size times the branch's true `X` degree. -/
theorem separabilityCertificate_xNatDegree_le
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) :
    (Polynomial.Bivariate.swap
      (separabilityCertificate factor)).natDegree ≤
      (factor.natDegree + factor.derivative.natDegree) *
        (trivariateXOuterEquiv K factor).natDegree := by
  have resultantMap := Polynomial.resultant_map_map
    factor factor.derivative factor.natDegree factor.derivative.natDegree
    (Polynomial.Bivariate.swap (R := K)).toRingHom
  change (Polynomial.Bivariate.swap
    (Polynomial.resultant factor factor.derivative factor.natDegree
      factor.derivative.natDegree)).natDegree ≤ _
  have swappedResultant : Polynomial.Bivariate.swap
      (Polynomial.resultant factor factor.derivative factor.natDegree
        factor.derivative.natDegree) =
      Polynomial.resultant (reorderFactorCoefficients K factor)
        ((factor.derivative).map
          (Polynomial.Bivariate.swap (R := K)).toRingHom)
        factor.natDegree factor.derivative.natDegree := by
    change Polynomial.resultant (reorderFactorCoefficients K factor)
      ((factor.derivative).map
        (Polynomial.Bivariate.swap (R := K)).toRingHom)
      factor.natDegree factor.derivative.natDegree =
        Polynomial.Bivariate.swap
          (Polynomial.resultant factor factor.derivative factor.natDegree
            factor.derivative.natDegree) at resultantMap
    exact resultantMap.symm
  rw [swappedResultant]
  exact resultant_natDegree_le_of_coeff_natDegree_le
    (reorderFactorCoefficients K factor)
    ((factor.derivative).map
      (Polynomial.Bivariate.swap (R := K)).toRingHom)
    factor.natDegree factor.derivative.natDegree
    (trivariateXOuterEquiv K factor).natDegree
    (reorderFactorCoefficients_coeff_natDegree_le factor)
    (reorderFactorDerivative_coeff_natDegree_le factor)

/-! The corresponding `Z`-degree bounds are needed to count the challenge
specializations at which the certificate vanishes. -/

/-- Reorder `K[X,Z,Y]` so that `Z` is the outer variable. -/
noncomputable def trivariateZOuterEquiv (K : Type*) [Field K] :
    TrivariatePolynomial K ≃ₐ[K] TrivariatePolynomial K :=
  (Polynomial.Bivariate.swap (R := Polynomial K)).restrictScalars K

theorem trivariateZOuterEquiv_monomial
    {K : Type*} [Field K] (yExponent zExponent xExponent : Nat) (value : K) :
    trivariateZOuterEquiv K
        (Polynomial.monomial yExponent
          (Polynomial.monomial zExponent
            (Polynomial.monomial xExponent value))) =
      Polynomial.monomial zExponent
        (Polynomial.monomial yExponent
          (Polynomial.monomial xExponent value)) := by
  change Polynomial.Bivariate.swap
      (Polynomial.monomial yExponent
        (Polynomial.monomial zExponent
          (Polynomial.monomial xExponent value))) = _
  rw [Polynomial.Bivariate.swap_monomial_monomial]

/-- The finite curve-interpolant representation records its genuine strict
challenge-degree bound. -/
theorem curveTrivariatePolynomial_zNatDegree_lt
    {K : Type*} [Field K]
    {maximumDegree curveDegree xBound yRows zBound : Nat}
    (zBoundPositive : 0 < zBound)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) :
    (trivariateZOuterEquiv K
      (curveTrivariatePolynomial coefficients)).natDegree < zBound := by
  classical
  refine lt_of_le_of_lt (b := zBound - 1) ?_ (by omega)
  unfold curveTrivariatePolynomial
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro monomial _
  rw [trivariateZOuterEquiv_monomial]
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- A global factor cannot acquire more `Z` degree than its parent. -/
theorem curvePrimeFactor_zNatDegree_le
    {K : Type*} [Field K]
    (polynomial factor : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial) :
    (trivariateZOuterEquiv K factor).natDegree ≤
      (trivariateZOuterEquiv K polynomial).natDegree := by
  have associatedProduct :=
    curvePrimeFactors_product_associated polynomial polynomialNeZero
  have factorDvd : factor ∣ polynomial :=
    (Multiset.dvd_prod factorMem).trans associatedProduct.dvd
  have mappedDvd := _root_.map_dvd
    (trivariateZOuterEquiv K).toRingHom factorDvd
  exact Polynomial.natDegree_le_of_dvd mappedDvd
    (by simpa using (trivariateZOuterEquiv K).injective.ne polynomialNeZero)

theorem factorCoefficient_zNatDegree_le
    {K : Type*} [Field K] (factor : TrivariatePolynomial K)
    (coefficient : Nat) :
    (factor.coeff coefficient).natDegree ≤
      (trivariateZOuterEquiv K factor).natDegree := by
  exact coeff_natDegree_le_bivariate_swap_natDegree factor coefficient

theorem factorDerivativeCoefficient_zNatDegree_le
    {K : Type*} [Field K] (factor : TrivariatePolynomial K)
    (coefficient : Nat) :
    ((factor.derivative).coeff coefficient).natDegree ≤
      (trivariateZOuterEquiv K factor).natDegree := by
  rw [Polynomial.coeff_derivative]
  calc
    (factor.coeff (coefficient + 1) *
        ((coefficient : Polynomial (Polynomial K)) + 1)).natDegree ≤
        (factor.coeff (coefficient + 1)).natDegree +
          ((coefficient : Polynomial (Polynomial K)) + 1).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (trivariateZOuterEquiv K factor).natDegree + 0 := by
      gcongr
      · exact factorCoefficient_zNatDegree_le factor (coefficient + 1)
      · have castSuccessor :
            ((coefficient : Polynomial (Polynomial K)) + 1) =
              ((coefficient + 1 : Nat) : Polynomial (Polynomial K)) := by
          norm_cast
        rw [castSuccessor, Polynomial.natDegree_natCast]
    _ = (trivariateZOuterEquiv K factor).natDegree := by omega

/-- Explicit `Z`-degree bound for the separability certificate. -/
theorem separabilityCertificate_zNatDegree_le
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) :
    (separabilityCertificate factor).natDegree ≤
      (factor.natDegree + factor.derivative.natDegree) *
        (trivariateZOuterEquiv K factor).natDegree := by
  exact resultant_natDegree_le_of_coeff_natDegree_le
    factor factor.derivative factor.natDegree factor.derivative.natDegree
    (trivariateZOuterEquiv K factor).natDegree
    (factorCoefficient_zNatDegree_le factor)
    (factorDerivativeCoefficient_zNatDegree_le factor)

/-- A nonzero polynomial over `K[Z]` whose `X` degree is smaller than `|K|`
cannot vanish at every constant `X = x`. -/
theorem exists_constant_eval_ne_zero_of_natDegree_lt_card
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (polynomial : Polynomial (Polynomial K))
    (polynomialNeZero : polynomial ≠ 0)
    (degreeSmall : polynomial.natDegree < Fintype.card K) :
    ∃ x : K, polynomial.eval (C x) ≠ 0 := by
  classical
  by_contra noPoint
  push Not at noPoint
  let constants : Finset (Polynomial K) := Finset.univ.image C
  have constantsCard : constants.card = Fintype.card K := by
    dsimp only [constants]
    calc
      (Finset.univ.image C).card = Finset.univ.card :=
        Finset.card_image_of_injective Finset.univ Polynomial.C_injective
      _ = Fintype.card K := Finset.card_univ
  have constantsAreRoots : constants.val ⊆ polynomial.roots := by
    intro constant constantMem
    rw [Polynomial.mem_roots polynomialNeZero]
    have constantMem' : constant ∈ constants := constantMem
    simp only [constants, Finset.mem_image] at constantMem'
    obtain ⟨x, _, rfl⟩ := constantMem'
    exact noPoint x
  have tooManyRoots :=
    Polynomial.card_le_degree_of_subset_roots constantsAreRoots
  rw [constantsCard] at tooManyRoots
  omega

/-- For an exact V7 interpolant branch, there is a uniform `X = x₀` at
which its separability certificate remains a nonzero polynomial in `Z`.
The numerical proof uses the exact bounds `deg_Y < 113`, `deg_X < 114688`
and the exact QM31 cardinality. -/
theorem exists_exactV7_uniformSmoothEvaluationPoint
    (polynomial factor : TrivariatePolynomial QM31Exact)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial)
    (factorPositive : 0 < factor.natDegree)
    (polynomialYDegreeSmall : polynomial.natDegree < 113)
    (polynomialXDegreeSmall :
      (trivariateXOuterEquiv QM31Exact polynomial).natDegree < 114688) :
    ∃ x₀ : QM31Exact,
      (Polynomial.Bivariate.swap
        (separabilityCertificate factor)).eval (C x₀) ≠ 0 := by
  have derivativeNeZero : factor.derivative ≠ 0 :=
    exactV7_curvePrimeFactor_derivative_ne_zero polynomial factor
      polynomialNeZero factorMem factorPositive polynomialYDegreeSmall
  have certificateNeZero : separabilityCertificate factor ≠ 0 :=
    separabilityCertificate_ne_zero polynomial factor polynomialNeZero
      factorMem factorPositive derivativeNeZero
  have swappedCertificateNeZero : Polynomial.Bivariate.swap
      (separabilityCertificate factor) ≠ 0 := by
    simpa using (Polynomial.Bivariate.swap (R := QM31Exact)).injective.ne
      certificateNeZero
  have factorYDegreeLe : factor.natDegree ≤ 112 :=
    (curvePrimeFactor_natDegree_le polynomial factor polynomialNeZero
      factorMem).trans (by omega)
  have derivativeDegreeLe : factor.derivative.natDegree ≤ 111 :=
    (Polynomial.natDegree_derivative_le factor).trans (by omega)
  have factorXDegreeLe :
      (trivariateXOuterEquiv QM31Exact factor).natDegree ≤ 114687 :=
    (curvePrimeFactor_xNatDegree_le polynomial factor polynomialNeZero
      factorMem).trans (by omega)
  have certificateDegreeLe :
      (Polynomial.Bivariate.swap
        (separabilityCertificate factor)).natDegree ≤ 223 * 114687 :=
    (separabilityCertificate_xNatDegree_le factor).trans <|
      Nat.mul_le_mul (by omega) factorXDegreeLe
  have certificateDegreeSmall :
      (Polynomial.Bivariate.swap
        (separabilityCertificate factor)).natDegree <
          Fintype.card QM31Exact := by
    rw [qm31Exact_card]
    exact certificateDegreeLe.trans_lt (by norm_num [P])
  exact exists_constant_eval_ne_zero_of_natDegree_lt_card
    (Polynomial.Bivariate.swap (separabilityCertificate factor))
    swappedCertificateNeZero certificateDegreeSmall

/-! ## Ordinary roots versus simple specialized roots -/

/-- Evaluate the innermost `X` variable of a coefficient in `K[X,Z]`,
leaving a polynomial in `Z`. -/
def evaluateInnerVariable
    {K : Type*} [Field K] (x : K) :
    Polynomial (Polynomial K) →+* Polynomial K :=
  Polynomial.mapRingHom (Polynomial.evalRingHom x)

/-- Evaluate the innermost `X` variable of a trivariate polynomial, leaving
an ordinary bivariate polynomial in `Z,Y`. -/
def specializeEvaluationPoint
    {K : Type*} [Field K] (x : K) :
    TrivariatePolynomial K →+* BivariatePolynomial K :=
  Polynomial.mapRingHom (evaluateInnerVariable x)

/-- Evaluate both `X` and the challenge `Z`, leaving a polynomial in the
candidate variable `Y`. -/
def specializeEvaluationPointChallenge
    {K : Type*} [Field K] (x z : K) :
    TrivariatePolynomial K →+* Polynomial K :=
  (Polynomial.mapRingHom (Polynomial.evalRingHom z)).comp
    (specializeEvaluationPoint x)

/-- Evaluating `X` and `Z` commutes.  This elementary identity is kept
explicit because it connects a challenge-dependent polynomial candidate to
the scalar candidate value used by the simple-root argument. -/
theorem map_evalInner_eval_eq_eval_eval
    {K : Type*} [Field K] (polynomial : Polynomial (Polynomial K))
    (x z : K) :
    (polynomial.map (Polynomial.evalRingHom x)).eval z =
      (polynomial.eval (C z)).eval x := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp [leftInduction, rightInduction]
  | monomial exponent coefficient =>
      simp [eval_monomial]

/-- Full trivariate evaluation agrees whether `X,Z` are specialized first,
or `Z` is specialized before substituting the candidate polynomial and then
evaluating at `X=x`. -/
theorem specializeEvaluationPointChallenge_eval_candidate
    {K : Type*} [Field K] (factor : TrivariatePolynomial K)
    (x z : K) (candidate : K[X]) :
    (specializeEvaluationPointChallenge x z factor).eval
        (candidate.eval x) =
      (challengeCandidateHom z candidate factor).eval x := by
  induction factor using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp [map_add, eval_add, leftInduction, rightInduction]
  | monomial exponent coefficient =>
      simp [specializeEvaluationPointChallenge,
        specializeEvaluationPoint, evaluateInnerVariable,
        challengeCandidateHom, specializeChallenge, substituteCandidate,
        eval_monomial, map_evalInner_eval_eq_eval_eval]

/-- Swapping `X,Z` and evaluating the new outer `X` is exactly coefficient-
wise evaluation of the original inner `X`. -/
theorem evaluateInnerVariable_eq_swap_eval
    {K : Type*} [Field K] (polynomial : Polynomial (Polynomial K))
    (x : K) :
    evaluateInnerVariable x polynomial =
      (Polynomial.Bivariate.swap polynomial).eval (C x) := by
  have swapped := Polynomial.Bivariate.aveal_eq_map_swap (R := K) x
    (Polynomial.Bivariate.swap polynomial)
  rw [Polynomial.Bivariate.swap_swap_apply] at swapped
  simpa [evaluateInnerVariable, Polynomial.aeval_def] using swapped.symm

/-- The resultant after specializing `X=x` is literally the univariate-in-
`Z` certificate selected above. -/
theorem specialized_resultant_eq_certificate_eval_x
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) (x : K) :
    Polynomial.resultant
        (specializeEvaluationPoint x factor)
        (specializeEvaluationPoint x factor.derivative)
        factor.natDegree factor.derivative.natDegree =
      (Polynomial.Bivariate.swap
        (separabilityCertificate factor)).eval (C x) := by
  change Polynomial.resultant
      (factor.map (evaluateInnerVariable x))
      (factor.derivative.map (evaluateInnerVariable x)) _ _ = _
  rw [Polynomial.resultant_map_map]
  exact evaluateInnerVariable_eq_swap_eval _ _

/-- The same certificate identity after also fixing the challenge `Z=z`. -/
theorem specialized_resultant_eq_certificate_eval_x_z
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) (x z : K) :
    Polynomial.resultant
        (specializeEvaluationPointChallenge x z factor)
        (specializeEvaluationPointChallenge x z factor.derivative)
        factor.natDegree factor.derivative.natDegree =
      ((Polynomial.Bivariate.swap
        (separabilityCertificate factor)).eval (C x)).eval z := by
  change Polynomial.resultant
      ((specializeEvaluationPoint x factor).map
        (Polynomial.evalRingHom z))
      ((specializeEvaluationPoint x factor.derivative).map
        (Polynomial.evalRingHom z)) _ _ = _
  rw [Polynomial.resultant_map_map]
  exact congrArg (Polynomial.eval z)
    (specialized_resultant_eq_certificate_eval_x factor x)

/-- A common root forces every bounded-degree Sylvester resultant to vanish.
The positive first bound rules out the degenerate `0 × 0` Sylvester matrix.
This statement deliberately uses the explicit degree bounds supplied to the
resultant rather than silently assuming specialization preserved degree. -/
theorem resultant_eq_zero_of_common_root_of_natDegree_le
    {K : Type*} [Field K]
    (left right : K[X]) (leftDegree rightDegree : Nat) (root : K)
    (leftDegreePositive : 0 < leftDegree)
    (leftDegreeLe : left.natDegree ≤ leftDegree)
    (rightDegreeLe : right.natDegree ≤ rightDegree)
    (leftRoot : left.IsRoot root) (rightRoot : right.IsRoot root) :
    Polynomial.resultant left right leftDegree rightDegree = 0 := by
  by_cases leftExact : left.natDegree = leftDegree
  · have leftNeZero : left ≠ 0 := by
      intro leftZero
      simp [leftZero] at leftExact
      omega
    obtain ⟨quotient, factorization⟩ :=
      (Polynomial.dvd_iff_isRoot.mpr leftRoot)
    have quotientNeZero : quotient ≠ 0 := by
      intro quotientZero
      rw [quotientZero, mul_zero] at factorization
      exact leftNeZero factorization
    have linearNeZero : (X - C root : K[X]) ≠ 0 := X_sub_C_ne_zero root
    have productDegree :
        (X - C root : K[X]).natDegree + quotient.natDegree =
          leftDegree := by
      rw [← Polynomial.natDegree_mul linearNeZero quotientNeZero,
        ← factorization, leftExact]
    rw [← productDegree, factorization]
    rw [Polynomial.resultant_mul_left _ _ _ _ rightDegreeLe,
      Polynomial.natDegree_X_sub_C,
      Polynomial.resultant_X_sub_C_left right rightDegree root
        rightDegreeLe,
      rightRoot]
    simp
  · by_cases rightExact : right.natDegree = rightDegree
    · by_cases rightZero : right = 0
      · rw [rightZero, Polynomial.resultant_zero_right]
        simp [leftDegreePositive.ne']
      · obtain ⟨quotient, factorization⟩ :=
          (Polynomial.dvd_iff_isRoot.mpr rightRoot)
        have quotientNeZero : quotient ≠ 0 := by
          intro quotientZero
          rw [quotientZero, mul_zero] at factorization
          exact rightZero factorization
        have linearNeZero : (X - C root : K[X]) ≠ 0 :=
          X_sub_C_ne_zero root
        have productDegree :
            (X - C root : K[X]).natDegree + quotient.natDegree =
              rightDegree := by
          rw [← Polynomial.natDegree_mul linearNeZero quotientNeZero,
            ← factorization, rightExact]
        rw [← productDegree, factorization]
        rw [Polynomial.resultant_mul_right _ _ _ _ leftDegreeLe,
          Polynomial.natDegree_X_sub_C,
          Polynomial.resultant_X_sub_C_right left leftDegree root
            leftDegreeLe,
          leftRoot]
        simp
    · exact Polynomial.resultant_eq_zero_of_lt_lt _ _ _ _
        (lt_of_le_of_ne leftDegreeLe leftExact)
        (lt_of_le_of_ne rightDegreeLe rightExact)

theorem specializeEvaluationPointChallenge_derivative
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) (x z : K) :
    specializeEvaluationPointChallenge x z factor.derivative =
      (specializeEvaluationPointChallenge x z factor).derivative := by
  change
    (factor.derivative.map (evaluateInnerVariable x)).map
        (Polynomial.evalRingHom z) =
      ((factor.map (evaluateInnerVariable x)).map
        (Polynomial.evalRingHom z)).derivative
  rw [Polynomial.derivative_map, Polynomial.derivative_map]

/-- The explicit finite-characteristic simple-root predicate used by the
later lift.  It is strictly stronger than ordinary divisibility by
`Y - P_z(X)`: the specialized derivative must not vanish at the root. -/
def SimpleSpecializedRoot
    {K : Type*} [Field K] (factor : TrivariatePolynomial K)
    (x z : K) (candidate : K[X]) : Prop :=
  (specializeEvaluationPointChallenge x z factor).IsRoot
      (candidate.eval x) ∧
    ¬(specializeEvaluationPointChallenge x z factor).derivative.IsRoot
      (candidate.eval x)

/-- A challenge-dependent ordinary polynomial root becomes a simple scalar
root exactly away from the explicit resultant certificate's roots.  This is
the formal barrier preventing specialization collisions or multiplicity
changes from being treated as harmless. -/
theorem simpleSpecializedRoot_of_certificate_ne_zero
    {K : Type*} [Field K]
    (factor : TrivariatePolynomial K) (x z : K) (candidate : K[X])
    (factorPositive : 0 < factor.natDegree)
    (certificateAtChallenge :
      ((Polynomial.Bivariate.swap
        (separabilityCertificate factor)).eval (C x)).eval z ≠ 0)
    (candidateRoot : challengeCandidateHom z candidate factor = 0) :
    SimpleSpecializedRoot factor x z candidate := by
  have rootAtPoint :
      (specializeEvaluationPointChallenge x z factor).IsRoot
        (candidate.eval x) := by
    rw [IsRoot]
    have evaluatedRoot := congrArg (Polynomial.eval x) candidateRoot
    simpa only [map_zero, eval_zero] using
      (specializeEvaluationPointChallenge_eval_candidate
        factor x z candidate).trans evaluatedRoot
  refine ⟨rootAtPoint, ?_⟩
  intro derivativeRoot
  have mappedDerivativeRoot :
      (specializeEvaluationPointChallenge x z factor.derivative).IsRoot
        (candidate.eval x) := by
    rw [specializeEvaluationPointChallenge_derivative]
    exact derivativeRoot
  have resultantZero : Polynomial.resultant
      (specializeEvaluationPointChallenge x z factor)
      (specializeEvaluationPointChallenge x z factor.derivative)
      factor.natDegree factor.derivative.natDegree = 0 :=
    resultant_eq_zero_of_common_root_of_natDegree_le _ _ _ _ _
      factorPositive
      (Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le)
      (Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le)
      rootAtPoint mappedDerivativeRoot
  exact certificateAtChallenge
    ((specialized_resultant_eq_certificate_eval_x_z factor x z).symm.trans
      resultantZero)

/-- The exact finite set of challenge specializations at which a fixed
branch's simple-root certificate fails at `X=x`. -/
noncomputable def nonsimpleChallengeSet
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) (x : K) :
    Finset K := by
  classical
  exact (((Polynomial.Bivariate.swap
    (separabilityCertificate factor)).eval (C x)).roots).toFinset

theorem mem_nonsimpleChallengeSet_iff
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) (x z : K)
    (certificateAtPoint :
      (Polynomial.Bivariate.swap
        (separabilityCertificate factor)).eval (C x) ≠ 0) :
    z ∈ nonsimpleChallengeSet factor x ↔
      ((Polynomial.Bivariate.swap
        (separabilityCertificate factor)).eval (C x)).eval z = 0 := by
  classical
  simp [nonsimpleChallengeSet, Polynomial.mem_roots certificateAtPoint]

/-- The bad specializations are counted by the actual `Z` degree of the
resultant certificate, not by a characteristic-zero discriminant heuristic. -/
theorem nonsimpleChallengeSet_card_le_certificate_zNatDegree
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) (x : K) :
    (nonsimpleChallengeSet factor x).card ≤
      (separabilityCertificate factor).natDegree := by
  classical
  calc
    (nonsimpleChallengeSet factor x).card ≤
        ((Polynomial.Bivariate.swap
          (separabilityCertificate factor)).eval (C x)).roots.card := by
      exact Multiset.toFinset_card_le _
    _ ≤ ((Polynomial.Bivariate.swap
          (separabilityCertificate factor)).eval (C x)).natDegree :=
      Polynomial.card_roots'
        ((Polynomial.Bivariate.swap
          (separabilityCertificate factor)).eval (C x))
    _ = (evaluateInnerVariable x
          (separabilityCertificate factor)).natDegree := by
      rw [evaluateInnerVariable_eq_swap_eval]
    _ ≤ (separabilityCertificate factor).natDegree :=
      Polynomial.natDegree_map_le

theorem nonsimpleChallengeSet_card_le
    {K : Type*} [Field K] (factor : TrivariatePolynomial K) (x : K) :
    (nonsimpleChallengeSet factor x).card ≤
      (factor.natDegree + factor.derivative.natDegree) *
        (trivariateZOuterEquiv K factor).natDegree :=
  (nonsimpleChallengeSet_card_le_certificate_zNatDegree factor x).trans
    (separabilityCertificate_zNatDegree_le factor)

/-- Exact V7-range specialization bound in terms of the parent interpolant's
declared challenge degree. -/
theorem exactV7_nonsimpleChallengeSet_card_le
    (polynomial factor : TrivariatePolynomial QM31Exact) (x : QM31Exact)
    (zBound : Nat) (zBoundPositive : 0 < zBound)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial)
    (polynomialYDegreeSmall : polynomial.natDegree < 113)
    (polynomialZDegreeSmall :
      (trivariateZOuterEquiv QM31Exact polynomial).natDegree < zBound) :
    (nonsimpleChallengeSet factor x).card ≤ 223 * (zBound - 1) := by
  have factorYDegreeLe : factor.natDegree ≤ 112 :=
    (curvePrimeFactor_natDegree_le polynomial factor polynomialNeZero
      factorMem).trans (by omega)
  have derivativeDegreeLe : factor.derivative.natDegree ≤ 111 :=
    (Polynomial.natDegree_derivative_le factor).trans (by omega)
  have factorZDegreeLe :
      (trivariateZOuterEquiv QM31Exact factor).natDegree ≤ zBound - 1 :=
    (curvePrimeFactor_zNatDegree_le polynomial factor polynomialNeZero
      factorMem).trans (by omega)
  exact (nonsimpleChallengeSet_card_le factor x).trans <|
    Nat.mul_le_mul (by omega) factorZDegreeLe

theorem exactV7Initial_nonsimpleChallengeSet_card_le
    (polynomial factor : TrivariatePolynomial QM31Exact) (x : QM31Exact)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial)
    (polynomialYDegreeSmall : polynomial.natDegree < 113)
    (polynomialZDegreeSmall :
      (trivariateZOuterEquiv QM31Exact polynomial).natDegree < 117078) :
    (nonsimpleChallengeSet factor x).card ≤ 26108171 := by
  simpa using exactV7_nonsimpleChallengeSet_card_le polynomial factor x
    117078 (by norm_num) polynomialNeZero factorMem
    polynomialYDegreeSmall polynomialZDegreeSmall

theorem exactV7Final_nonsimpleChallengeSet_card_le
    (polynomial factor : TrivariatePolynomial QM31Exact) (x : QM31Exact)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial)
    (polynomialYDegreeSmall : polynomial.natDegree < 113)
    (polynomialZDegreeSmall :
      (trivariateZOuterEquiv QM31Exact polynomial).natDegree < 12594) :
    (nonsimpleChallengeSet factor x).card ≤ 2808239 := by
  simpa using exactV7_nonsimpleChallengeSet_card_le polynomial factor x
    12594 (by norm_num) polynomialNeZero factorMem
    polynomialYDegreeSmall polynomialZDegreeSmall

/-- Outside the counted exceptional set, an ordinary specialized candidate
root is a certified simple root. -/
theorem simpleSpecializedRoot_of_not_mem_nonsimpleChallengeSet
    {K : Type*} [Field K]
    (factor : TrivariatePolynomial K) (x z : K) (candidate : K[X])
    (factorPositive : 0 < factor.natDegree)
    (certificateAtPoint :
      (Polynomial.Bivariate.swap
        (separabilityCertificate factor)).eval (C x) ≠ 0)
    (challengeNotExceptional : z ∉ nonsimpleChallengeSet factor x)
    (candidateRoot : challengeCandidateHom z candidate factor = 0) :
    SimpleSpecializedRoot factor x z candidate := by
  apply simpleSpecializedRoot_of_certificate_ne_zero factor x z candidate
    factorPositive
  · intro certificateZero
    exact challengeNotExceptional <|
      (mem_nonsimpleChallengeSet_iff factor x z certificateAtPoint).mpr
        certificateZero
  · exact candidateRoot

#print axioms curvePrimeFactor_resultant_derivative_ne_zero
#print axioms separabilityCertificate_ne_zero
#print axioms separabilityCertificate_xNatDegree_le
#print axioms exists_exactV7_uniformSmoothEvaluationPoint
#print axioms resultant_eq_zero_of_common_root_of_natDegree_le
#print axioms simpleSpecializedRoot_of_certificate_ne_zero
#print axioms nonsimpleChallengeSet_card_le
#print axioms exactV7Initial_nonsimpleChallengeSet_card_le
#print axioms exactV7Final_nonsimpleChallengeSet_card_le
#print axioms simpleSpecializedRoot_of_not_mem_nonsimpleChallengeSet

end

end AspisK1.V7ExactCorrelatedAgreementSmooth
