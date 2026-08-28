import AspisFormal.K1.V7ExactCorrelatedAgreementInterpolation
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Polynomial factor boundary for exact V7 correlated agreement

This file converts the finite coefficient representation of the BCH+25
trivariate interpolant into ordinary iterated polynomial rings.  The outer
variable is `Y`, the middle variable is the batching challenge `Z`, and the
inner variable is the Reed--Solomon evaluation variable `X`.

The conversion is deliberately algebraic: specialization in `Z` is a ring
homomorphism, and substituting a candidate polynomial for `Y` is ordinary
polynomial evaluation.  Thus a challenge-dependent candidate root gives a
literal linear factor `Y - P_z(X)` of the specialized interpolant.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementFactors

open scoped BigOperators
open Polynomial
open AspisK1.V7Tag73ExactMultiplicityThreeGS
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisV5ComponentCQM31TowerExact

noncomputable section

private theorem monomial_fintype_sum
    {R ι : Type*} [Semiring R] [Fintype ι]
    (exponent : Nat) (values : ι → R) :
    Polynomial.monomial exponent (∑ index, values index) =
      ∑ index, Polynomial.monomial exponent (values index) := by
  classical
  ext coefficient
  by_cases same : exponent = coefficient
  · subst coefficient
    simp
  · simp [coeff_monomial, same]

private theorem curveMonomialIndex_ext
    (maximumDegree curveDegree xBound yRows zBound : Nat)
    (left right :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound)
    (row : left.1.1 = right.1.1)
    (xExponent : left.2.1.1 = right.2.1.1)
    (zExponent : left.2.2.1 = right.2.2.1) :
    left = right := by
  rcases left with ⟨leftRow, leftX, leftZ⟩
  rcases right with ⟨rightRow, rightX, rightZ⟩
  simp only at row xExponent zExponent ⊢
  have rowEquality : leftRow = rightRow := Fin.ext row
  subst rightRow
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  exact Prod.ext (Fin.ext xExponent) (Fin.ext zExponent)

private theorem weightedMonomialIndex_ext
    (maximumDegree weightedDegree ell : Nat)
    (left right : WeightedMonomialIndex maximumDegree weightedDegree ell)
    (row : left.1.1 = right.1.1)
    (xExponent : left.2.1 = right.2.1) :
    left = right := by
  rcases left with ⟨leftRow, leftX⟩
  rcases right with ⟨rightRow, rightX⟩
  simp only at row xExponent ⊢
  have rowEquality : leftRow = rightRow := Fin.ext row
  subst rightRow
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  exact Fin.ext xExponent

/-- A bivariate polynomial with inner variable `X` and outer variable `Y`. -/
abbrev BivariatePolynomial (K : Type*) [Semiring K] := Polynomial (Polynomial K)

/-- A trivariate polynomial with inner variable `X`, middle variable `Z`,
and outer variable `Y`. -/
abbrev TrivariatePolynomial (K : Type*) [Semiring K] :=
  Polynomial (Polynomial (Polynomial K))

/-- The ordinary bivariate polynomial represented by a weighted coefficient
vector. -/
def weightedBivariatePolynomial
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K) :
    BivariatePolynomial K :=
  ∑ monomial,
    Polynomial.monomial monomial.1.1
      (Polynomial.monomial monomial.2.1 (coefficients monomial))

/-- The ordinary trivariate polynomial represented by the curve coefficient
vector. -/
def curveTrivariatePolynomial
    {K : Type*} [Field K]
    {maximumDegree curveDegree xBound yRows zBound : Nat}
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) :
    TrivariatePolynomial K :=
  ∑ monomial,
    Polynomial.monomial monomial.1.1
      (Polynomial.monomial monomial.2.2.1
        (Polynomial.monomial monomial.2.1.1 (coefficients monomial)))

/-- Specialize the middle challenge variable of an iterated trivariate
polynomial. -/
def specializeChallenge
    {K : Type*} [Field K] (z : K) :
    TrivariatePolynomial K →+* BivariatePolynomial K :=
  Polynomial.mapRingHom (Polynomial.evalRingHom (C z))

/-- Substitute a candidate `P(X)` for the outer `Y` variable. -/
def substituteCandidate
    {K : Type*} [Field K] (candidate : K[X]) :
    BivariatePolynomial K →+* K[X] :=
  Polynomial.evalRingHom candidate

@[simp] theorem substituteCandidate_weightedBivariatePolynomial
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (candidate : K[X]) :
    substituteCandidate candidate
        (weightedBivariatePolynomial coefficients) =
      interpolationSubstitute coefficients candidate := by
  classical
  simp [substituteCandidate, weightedBivariatePolynomial,
    interpolationSubstitute, coe_evalRingHom, eval_monomial,
    C_mul_X_pow_eq_monomial]

@[simp] theorem specializeChallenge_curveTrivariatePolynomial
    {K : Type*} [Field K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (z : K) :
    specializeChallenge z (curveTrivariatePolynomial coefficients) =
      weightedBivariatePolynomial
        (specializeCurveCoefficients lastRow coefficients z) := by
  classical
  unfold specializeChallenge curveTrivariatePolynomial
  rw [map_sum]
  rw [← (weightedCurveIndexEquiv maximumDegree curveDegree weightedDegree ell
    zBound lastRow).sum_comp]
  simp only [Fintype.sum_sigma, map_monomial, coe_mapRingHom,
    coe_evalRingHom, eval_monomial,
    weightedCurveIndexEquiv_row, weightedCurveIndexEquiv_xExponent,
    weightedCurveIndexEquiv_zExponent]
  unfold weightedBivariatePolynomial
  simp only [specializeCurveCoefficients_apply]
  rw [Finset.sum_sigma']
  apply Finset.sum_congr rfl
  intro row _
  rw [map_sum]
  rw [monomial_fintype_sum]
  apply Finset.sum_congr rfl
  intro zExponent _
  simp only [← map_pow, monomial_mul_C]

/-- A zero candidate substitution is exactly a literal specialized root of
the ordinary outer-`Y` polynomial. -/
theorem candidate_isRoot_of_substitute_eq_zero
    {K : Type*} [Field K]
    (polynomial : BivariatePolynomial K) (candidate : K[X])
    (zero : substituteCandidate candidate polynomial = 0) :
    polynomial.IsRoot candidate := by
  exact zero

/-- Therefore the literal outer linear factor `Y - P(X)` divides the
specialized interpolant. -/
theorem candidate_linearFactor_dvd_of_substitute_eq_zero
    {K : Type*} [Field K]
    (polynomial : BivariatePolynomial K) (candidate : K[X])
    (zero : substituteCandidate candidate polynomial = 0) :
    X - C candidate ∣ polynomial := by
  rw [dvd_iff_isRoot]
  exact candidate_isRoot_of_substitute_eq_zero polynomial candidate zero

/-- The finite coefficient representation is nonzero exactly when the
ordinary iterated trivariate polynomial is nonzero.  This prevents the
factorization stage from acquiring a hidden nonzeroness premise. -/
theorem curveTrivariatePolynomial_ne_zero
    {K : Type*} [Field K]
    {maximumDegree curveDegree xBound yRows zBound : Nat}
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (coefficientsNeZero : coefficients ≠ 0) :
    curveTrivariatePolynomial coefficients ≠ 0 := by
  classical
  intro polynomialZero
  apply coefficientsNeZero
  funext monomial
  change coefficients monomial = 0
  have coefficientZero := congrArg
    (fun polynomial : TrivariatePolynomial K =>
      ((polynomial.coeff monomial.1.1).coeff monomial.2.2.1).coeff
        monomial.2.1.1) polynomialZero
  simp only [curveTrivariatePolynomial, Polynomial.coeff_zero] at coefficientZero
  change (Polynomial.lcoeff K monomial.2.1.1)
      ((Polynomial.lcoeff (Polynomial K) monomial.2.2.1)
        ((Polynomial.lcoeff (Polynomial (Polynomial K)) monomial.1.1)
          (∑ other,
            Polynomial.monomial other.1.1
              (Polynomial.monomial other.2.2.1
                (Polynomial.monomial other.2.1.1
                  (coefficients other)))))) = 0 at coefficientZero
  rw [map_sum, map_sum, map_sum] at coefficientZero
  simp only [Polynomial.lcoeff_apply] at coefficientZero
  rw [Finset.sum_eq_single monomial] at coefficientZero
  · simpa only [coeff_monomial, if_pos] using coefficientZero
  · intro other _ otherNe
    simp only [coeff_monomial]
    by_cases row : other.1.1 = monomial.1.1
    · by_cases challenge : other.2.2.1 = monomial.2.2.1
      · have xNe : other.2.1.1 ≠ monomial.2.1.1 := by
          intro xEqual
          apply otherNe
          exact curveMonomialIndex_ext maximumDegree curveDegree xBound
            yRows zBound other monomial row xEqual challenge
        rw [if_pos row, coeff_monomial, if_pos challenge,
          coeff_monomial, if_neg xNe]
      · rw [if_pos row, coeff_monomial, if_neg challenge]
        rfl
    · rw [if_neg row]
      rfl
  · simp

/-- The weighted coefficient representation is injective. -/
theorem weightedBivariatePolynomial_ne_zero
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (coefficientsNeZero : coefficients ≠ 0) :
    weightedBivariatePolynomial coefficients ≠ 0 := by
  classical
  intro polynomialZero
  apply coefficientsNeZero
  funext monomial
  change coefficients monomial = 0
  have coefficientZero := congrArg
    (fun polynomial : BivariatePolynomial K =>
      (polynomial.coeff monomial.1.1).coeff monomial.2.1) polynomialZero
  simp only [weightedBivariatePolynomial, Polynomial.coeff_zero] at coefficientZero
  change (Polynomial.lcoeff K monomial.2.1)
      ((Polynomial.lcoeff (Polynomial K) monomial.1.1)
        (∑ other,
          Polynomial.monomial other.1.1
            (Polynomial.monomial other.2.1 (coefficients other)))) =
      (0 : K) at coefficientZero
  rw [map_sum, map_sum] at coefficientZero
  simp only [Polynomial.lcoeff_apply] at coefficientZero
  rw [Finset.sum_eq_single monomial] at coefficientZero
  · simpa only [coeff_monomial, if_pos] using coefficientZero
  · intro other _ otherNe
    simp only [coeff_monomial]
    by_cases row : other.1.1 = monomial.1.1
    · have xNe : other.2.1 ≠ monomial.2.1 := by
        intro xEqual
        apply otherNe
        exact weightedMonomialIndex_ext maximumDegree weightedDegree ell
          other monomial row xEqual
      rw [if_pos row, coeff_monomial, if_neg xNe]
    · rw [if_neg row]
      rfl
  · simp

/-- The outer `Y` degree is strictly below the declared number of rows. -/
theorem curveTrivariatePolynomial_natDegree_lt
    {K : Type*} [Field K]
    {maximumDegree curveDegree xBound yRows zBound : Nat}
    (yRowsPositive : 0 < yRows)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) :
    (curveTrivariatePolynomial coefficients).natDegree < yRows := by
  classical
  refine lt_of_le_of_lt (b := yRows - 1) ?_ (by omega)
  unfold curveTrivariatePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro monomial _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- First specialize `Z`, then substitute a candidate for `Y`. -/
def challengeCandidateHom
    {K : Type*} [Field K] (z : K) (candidate : K[X]) :
    TrivariatePolynomial K →+* K[X] :=
  (substituteCandidate candidate).comp (specializeChallenge z)

/-- A fixed prime-factor multiset for a nonzero trivariate polynomial.  The
choice is mathematical and independent of every later challenge. -/
noncomputable def curvePrimeFactors
    {K : Type*} [Field K] (polynomial : TrivariatePolynomial K) :
    Multiset (TrivariatePolynomial K) := by
  classical
  exact if zero : polynomial = 0 then 0
    else Classical.choose
      (UniqueFactorizationMonoid.exists_prime_factors polynomial zero)

theorem curvePrimeFactors_prime
    {K : Type*} [Field K] (polynomial : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0) :
    ∀ factor ∈ curvePrimeFactors polynomial, Prime factor := by
  unfold curvePrimeFactors
  rw [dif_neg polynomialNeZero]
  exact (Classical.choose_spec
    (UniqueFactorizationMonoid.exists_prime_factors polynomial
      polynomialNeZero)).1

theorem curvePrimeFactors_product_associated
    {K : Type*} [Field K] (polynomial : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0) :
    Associated (curvePrimeFactors polynomial).prod polynomial := by
  unfold curvePrimeFactors
  rw [dif_neg polynomialNeZero]
  exact (Classical.choose_spec
    (UniqueFactorizationMonoid.exists_prime_factors polynomial
      polynomialNeZero)).2

/-- The members of the fixed global factorization that genuinely depend on
the outer candidate variable `Y`.  This is the finite family into which good
challenges are pigeonholed. -/
noncomputable def positiveYPrimeFactors
    {K : Type*} [Field K] (polynomial : TrivariatePolynomial K) :
    Multiset (TrivariatePolynomial K) :=
  (curvePrimeFactors polynomial).filter (fun factor => 0 < factor.natDegree)

@[simp] theorem mem_positiveYPrimeFactors
    {K : Type*} [Field K] (polynomial factor : TrivariatePolynomial K) :
    factor ∈ positiveYPrimeFactors polynomial ↔
      factor ∈ curvePrimeFactors polynomial ∧ 0 < factor.natDegree := by
  classical
  simp [positiveYPrimeFactors]

private theorem card_filter_positive_le_sum_map
    {α : Type*} (values : Multiset α) (weight : α → Nat) :
    (values.filter (fun value => 0 < weight value)).card ≤
      (values.map weight).sum := by
  classical
  induction values using Multiset.induction_on with
  | empty => simp
  | @cons value values induction =>
      by_cases positive : 0 < weight value
      · simp [positive]
        omega
      · simpa [positive] using
          induction.trans (Nat.le_add_left _ (weight value))

/-- There are at most `deg_Y Q` positive-`Y` branches in the fixed global
factorization.  Multiplicity is retained: this counts the actual prime-factor
multiset selected before any challenge is specialized. -/
theorem positiveYPrimeFactors_card_le_natDegree
    {K : Type*} [Field K] (polynomial : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0) :
    (positiveYPrimeFactors polynomial).card ≤ polynomial.natDegree := by
  classical
  let factors := curvePrimeFactors polynomial
  have factorsPrime : ∀ factor ∈ factors, Prime factor :=
    curvePrimeFactors_prime polynomial polynomialNeZero
  have zeroNotMem : (0 : TrivariatePolynomial K) ∉ factors := by
    intro zeroMem
    exact (factorsPrime 0 zeroMem).ne_zero rfl
  have productDegree : factors.prod.natDegree =
      (factors.map Polynomial.natDegree).sum :=
    Polynomial.natDegree_multiset_prod factors zeroNotMem
  have associatedProduct : Associated factors.prod polynomial :=
    curvePrimeFactors_product_associated polynomial polynomialNeZero
  have degreeEquality : factors.prod.natDegree = polynomial.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated associatedProduct)
  calc
    (positiveYPrimeFactors polynomial).card =
        (factors.filter (fun factor => 0 < factor.natDegree)).card := rfl
    _ ≤ (factors.map Polynomial.natDegree).sum :=
      card_filter_positive_le_sum_map factors Polynomial.natDegree
    _ = factors.prod.natDegree := productDegree.symm
    _ = polynomial.natDegree := degreeEquality

/-- The sum of the literal positive-`Y` branch degrees, with multiplicity,
is the parent `Y` degree.  The weak form is convenient for additive branch
budgets. -/
theorem sum_positiveYPrimeFactors_natDegree_le
    {K : Type*} [Field K] (polynomial : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0) :
    ((positiveYPrimeFactors polynomial).map Polynomial.natDegree).sum ≤
      polynomial.natDegree := by
  classical
  let factors := curvePrimeFactors polynomial
  have factorsPrime : ∀ factor ∈ factors, Prime factor :=
    curvePrimeFactors_prime polynomial polynomialNeZero
  have zeroNotMem : (0 : TrivariatePolynomial K) ∉ factors := by
    intro zeroMem
    exact (factorsPrime 0 zeroMem).ne_zero rfl
  have productDegree : factors.prod.natDegree =
      (factors.map Polynomial.natDegree).sum :=
    Polynomial.natDegree_multiset_prod factors zeroNotMem
  have associatedProduct : Associated factors.prod polynomial :=
    curvePrimeFactors_product_associated polynomial polynomialNeZero
  have degreeEquality : factors.prod.natDegree = polynomial.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated associatedProduct)
  have filteredLe :
      (((factors.filter fun factor => 0 < factor.natDegree).map
          Polynomial.natDegree).sum) ≤
        (factors.map Polynomial.natDegree).sum := by
    induction factors using Multiset.induction_on with
    | empty => simp
    | @cons factor factors induction =>
        by_cases positive : 0 < factor.natDegree
        · simp [positive, induction]
        · simp [positive]
          exact induction.trans (Nat.le_add_left _ _)
  exact filteredLe.trans_eq (productDegree.symm.trans degreeEquality)

/-- A member of the fixed global factorization cannot have larger outer
`Y` degree than the original polynomial. -/
theorem curvePrimeFactor_natDegree_le
    {K : Type*} [Field K] (polynomial factor : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial) :
    factor.natDegree ≤ polynomial.natDegree := by
  have associatedProduct :=
    curvePrimeFactors_product_associated polynomial polynomialNeZero
  have factorDvd : factor ∣ polynomial :=
    (Multiset.dvd_prod factorMem).trans associatedProduct.dvd
  exact Polynomial.natDegree_le_of_dvd factorDvd polynomialNeZero

/-- Explicit positive-characteristic derivative criterion.  No
characteristic-zero typeclass is used: the leading `Y` exponent is required
to have a nonzero cast in the coefficient domain. -/
theorem derivative_ne_zero_of_natDegree_pos_of_cast_ne_zero
    {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (polynomial : R[X]) (degreePositive : 0 < polynomial.natDegree)
    (degreeCastNeZero : (polynomial.natDegree : R) ≠ 0) :
    polynomial.derivative ≠ 0 := by
  intro derivativeZero
  have polynomialNeZero : polynomial ≠ 0 := by
    intro polynomialZero
    rw [polynomialZero] at degreePositive
    simp at degreePositive
  have coefficientZero := congrArg
    (fun derivative : R[X] => derivative.coeff (polynomial.natDegree - 1))
    derivativeZero
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at coefficientZero
  have predecessor : polynomial.natDegree - 1 + 1 = polynomial.natDegree := by
    omega
  rw [predecessor] at coefficientZero
  have castPredecessor :
      ((polynomial.natDegree - 1 : Nat) : R) + 1 =
        (polynomial.natDegree : R) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun value : Nat => (value : R)) predecessor
  rw [castPredecessor] at coefficientZero
  change polynomial.leadingCoeff * (polynomial.natDegree : R) = 0 at coefficientZero
  exact (mul_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr polynomialNeZero)
    degreeCastNeZero) coefficientZero

/-- Every positive natural below the deployed M31 characteristic remains
nonzero in the exact released quartic field. -/
theorem qm31Exact_natCast_ne_zero_of_pos_of_lt_characteristic
    (degree : Nat) (degreePositive : 0 < degree) (degreeSmall : degree < P) :
    (degree : QM31Exact) ≠ 0 := by
  have baseNonzero : (degree : M31Exact) ≠ 0 := by
    intro castZero
    have divides := (CharP.cast_eq_zero_iff M31Exact P degree).mp castZero
    exact (Nat.not_dvd_of_pos_of_lt degreePositive degreeSmall) divides
  intro towerZero
  apply baseNonzero
  apply FaithfulSMul.algebraMap_injective M31Exact QM31Exact
  calc
    algebraMap M31Exact QM31Exact (degree : M31Exact) =
        (degree : QM31Exact) := map_natCast _ degree
    _ = 0 := towerZero
    _ = algebraMap M31Exact QM31Exact (0 : M31Exact) :=
      (map_zero _).symm

/-- The same explicit characteristic guard in the coefficient ring
`QM31[X,Z]` of the outer `Y` polynomial. -/
theorem trivariateCoefficient_natCast_ne_zero_of_pos_of_lt_characteristic
    (degree : Nat) (degreePositive : 0 < degree) (degreeSmall : degree < P) :
    (degree : Polynomial (Polynomial QM31Exact)) ≠ 0 := by
  have baseNonzero :=
    qm31Exact_natCast_ne_zero_of_pos_of_lt_characteristic degree
      degreePositive degreeSmall
  intro coefficientZero
  apply baseNonzero
  have constantCoefficientZero := congrArg
    (fun coefficient : Polynomial (Polynomial QM31Exact) =>
      (coefficient.coeff 0).coeff 0) coefficientZero
  simpa using constantCoefficientZero

/-- For the exact V7 degree range, every positive-`Y` global prime factor is
separable in `Y`: its derivative is kernel-proved nonzero using
`char(QM31)=2147483647`, not characteristic-zero intuition. -/
theorem exactV7_curvePrimeFactor_derivative_ne_zero
    (polynomial factor : TrivariatePolynomial QM31Exact)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ curvePrimeFactors polynomial)
    (factorPositive : 0 < factor.natDegree)
    (polynomialDegreeSmall : polynomial.natDegree < 113) :
    factor.derivative ≠ 0 := by
  have factorDegreeLe := curvePrimeFactor_natDegree_le polynomial factor
    polynomialNeZero factorMem
  have factorDegreeSmall : factor.natDegree < P :=
    factorDegreeLe.trans_lt <| polynomialDegreeSmall.trans <| by
      norm_num [P]
  exact derivative_ne_zero_of_natDegree_pos_of_cast_ne_zero factor
    factorPositive
    (trivariateCoefficient_natCast_ne_zero_of_pos_of_lt_characteristic
      factor.natDegree factorPositive factorDegreeSmall)

/-- A normalized irreducible factor carries every specialized candidate
root of a nonzero specialization.  The selected factor necessarily has
positive `Y` degree; a `Y`-constant factor could only vanish by making the
whole specialization zero. -/
theorem exists_positiveDegree_primeFactor_root
    {K : Type*} [Field K]
    (polynomial : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0)
    (z : K) (candidate : K[X])
    (specializationNeZero : specializeChallenge z polynomial ≠ 0)
    (candidateRoot : challengeCandidateHom z candidate polynomial = 0) :
    ∃ factor ∈ curvePrimeFactors polynomial,
      0 < factor.natDegree ∧
        challengeCandidateHom z candidate factor = 0 := by
  classical
  let factors := curvePrimeFactors polynomial
  have associatedProduct : Associated factors.prod polynomial :=
    curvePrimeFactors_product_associated polynomial polynomialNeZero
  have mappedAssociated := associatedProduct.map
    (challengeCandidateHom z candidate)
  have mappedProductZero :
      (factors.map (challengeCandidateHom z candidate)).prod = 0 := by
    rw [← map_multiset_prod]
    exact mappedAssociated.eq_zero_iff.mpr candidateRoot
  have zeroMem : (0 : K[X]) ∈
      factors.map (challengeCandidateHom z candidate) :=
    Multiset.prod_eq_zero_iff.mp mappedProductZero
  rw [Multiset.mem_map] at zeroMem
  obtain ⟨factor, factorMem, factorRoot⟩ := zeroMem
  refine ⟨factor, factorMem, ?_, factorRoot⟩
  have factorDvd : factor ∣ polynomial :=
    (Multiset.dvd_prod factorMem).trans associatedProduct.dvd
  by_contra degreeNotPositive
  have degreeZero : factor.natDegree = 0 := by omega
  have factorConstant : factor = C (factor.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero degreeZero
  have specializedFactorZero : specializeChallenge z factor = 0 := by
    rw [factorConstant] at factorRoot ⊢
    simpa [challengeCandidateHom, substituteCandidate, specializeChallenge,
      coe_evalRingHom] using factorRoot
  have specializedDvd : specializeChallenge z factor ∣
      specializeChallenge z polynomial := _root_.map_dvd _ factorDvd
  rw [specializedFactorZero, zero_dvd_iff] at specializedDvd
  exact specializationNeZero specializedDvd

/-- Pigeonhole challenge-dependent candidate roots into the correct fixed
global irreducible branch.  The conclusion counts challenges on which one
particular factor of the original trivariate polynomial vanishes after both
specializations; it does not merely count the existence of unrelated linear
factors after specialization. -/
theorem exists_frequent_positiveDegree_primeFactor
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (polynomial : TrivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0)
    (candidate : K → K[X]) (challenges : Finset K) (branchTarget : Nat)
    (specializationNeZero : ∀ z ∈ challenges,
      specializeChallenge z polynomial ≠ 0)
    (candidateRoot : ∀ z ∈ challenges,
      challengeCandidateHom z (candidate z) polynomial = 0)
    (many : polynomial.natDegree * branchTarget < challenges.card) :
    ∃ factor ∈ curvePrimeFactors polynomial,
      0 < factor.natDegree ∧ branchTarget <
        (challenges.filter fun z =>
          challengeCandidateHom z (candidate z) factor = 0).card := by
  classical
  have branchExists : ∀ z ∈ challenges,
      ∃ factor ∈ positiveYPrimeFactors polynomial,
        challengeCandidateHom z (candidate z) factor = 0 := by
    intro z zMem
    obtain ⟨factor, factorMem, factorDegree, factorRoot⟩ :=
      exists_positiveDegree_primeFactor_root polynomial polynomialNeZero z
        (candidate z) (specializationNeZero z zMem) (candidateRoot z zMem)
    exact ⟨factor,
      (mem_positiveYPrimeFactors polynomial factor).mpr
        ⟨factorMem, factorDegree⟩,
      factorRoot⟩
  let selectedFactor : K → TrivariatePolynomial K := fun z =>
    if zMem : z ∈ challenges then Classical.choose (branchExists z zMem)
    else polynomial
  have selectedFactorSpec : ∀ z ∈ challenges,
      selectedFactor z ∈ positiveYPrimeFactors polynomial ∧
        challengeCandidateHom z (candidate z) (selectedFactor z) = 0 := by
    intro z zMem
    simp only [selectedFactor, dif_pos zMem]
    exact Classical.choose_spec (branchExists z zMem)
  let branches := (positiveYPrimeFactors polynomial).toFinset
  have selectedMaps : ∀ z ∈ challenges, selectedFactor z ∈ branches := by
    intro z zMem
    simpa only [branches, Multiset.mem_toFinset] using
      (selectedFactorSpec z zMem).1
  have branchCardLe : branches.card ≤ polynomial.natDegree :=
    (Multiset.toFinset_card_le (positiveYPrimeFactors polynomial)).trans
      (positiveYPrimeFactors_card_le_natDegree polynomial polynomialNeZero)
  have enoughForPigeonhole : branches.card * branchTarget < challenges.card :=
    (Nat.mul_le_mul_right branchTarget branchCardLe).trans_lt many
  obtain ⟨factor, factorMem, frequentFiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := challenges) (t := branches) (f := selectedFactor)
      selectedMaps enoughForPigeonhole
  have factorPositiveMem : factor ∈ positiveYPrimeFactors polynomial := by
    simpa only [branches, Multiset.mem_toFinset] using factorMem
  have fiberSubset :
      challenges.filter (fun z => selectedFactor z = factor) ⊆
        challenges.filter (fun z =>
          challengeCandidateHom z (candidate z) factor = 0) := by
    intro z zMem
    rw [Finset.mem_filter] at zMem ⊢
    refine ⟨zMem.1, ?_⟩
    rw [← zMem.2]
    exact (selectedFactorSpec z zMem.1).2
  have frequentRoots : branchTarget <
      (challenges.filter fun z =>
        challengeCandidateHom z (candidate z) factor = 0).card :=
    frequentFiber.trans_le (Finset.card_le_card fiberSubset)
  exact ⟨factor,
    (mem_positiveYPrimeFactors polynomial factor).mp factorPositiveMem |>.1,
    (mem_positiveYPrimeFactors polynomial factor).mp factorPositiveMem |>.2,
    frequentRoots⟩

#print axioms specializeChallenge_curveTrivariatePolynomial
#print axioms candidate_linearFactor_dvd_of_substitute_eq_zero
#print axioms curveTrivariatePolynomial_ne_zero
#print axioms weightedBivariatePolynomial_ne_zero
#print axioms curveTrivariatePolynomial_natDegree_lt
#print axioms curvePrimeFactors_product_associated
#print axioms positiveYPrimeFactors_card_le_natDegree
#print axioms sum_positiveYPrimeFactors_natDegree_le
#print axioms exists_positiveDegree_primeFactor_root
#print axioms exists_frequent_positiveDegree_primeFactor

end

end AspisK1.V7ExactCorrelatedAgreementFactors
