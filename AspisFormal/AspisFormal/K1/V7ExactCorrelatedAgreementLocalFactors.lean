import AspisFormal.K1.V7ExactCorrelatedAgreementHensel
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Fixed local branches for exact V7 correlated agreement

After choosing one global irreducible branch `R(X,Y,Z)` and a uniform smooth
point `x₀`, this module factors the single bivariate polynomial
`R(x₀,Y,Z)`.  Challenge-dependent roots are pigeonholed into one member of
that fixed factorization.  Thus the branch counted here is not an arbitrary
linear factor appearing independently after each specialization.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementLocalFactors

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth

noncomputable section

/-- One fixed prime factorization of a nonzero bivariate polynomial, with
inner variable `Z` and outer variable `Y`. -/
noncomputable def bivariatePrimeFactors
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K) :
    Multiset (BivariatePolynomial K) := by
  classical
  exact if zero : polynomial = 0 then 0
    else Classical.choose
      (UniqueFactorizationMonoid.exists_prime_factors polynomial zero)

theorem bivariatePrimeFactors_prime
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0) :
    ∀ factor ∈ bivariatePrimeFactors polynomial, Prime factor := by
  unfold bivariatePrimeFactors
  rw [dif_neg polynomialNeZero]
  exact (Classical.choose_spec
    (UniqueFactorizationMonoid.exists_prime_factors polynomial
      polynomialNeZero)).1

theorem bivariatePrimeFactors_product_associated
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0) :
    Associated (bivariatePrimeFactors polynomial).prod polynomial := by
  unfold bivariatePrimeFactors
  rw [dif_neg polynomialNeZero]
  exact (Classical.choose_spec
    (UniqueFactorizationMonoid.exists_prime_factors polynomial
      polynomialNeZero)).2

/-- A member of the fixed local factorization contributes its literal
leading coefficient to the leading coefficient of the parent.  This is the
divisibility needed to remove the apparent final power of `W` from the
regularized Hensel derivative; it is derived from the actual factorization,
not supplied as a denominator hypothesis. -/
theorem exists_leadingCoeff_quotient_of_bivariatePrimeFactor
    {K : Type*} [Field K]
    (polynomial factor : BivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0)
    (factorMem : factor ∈ bivariatePrimeFactors polynomial) :
    ∃ quotientLeading : Polynomial K,
      quotientLeading ≠ 0 ∧
        factor.leadingCoeff * quotientLeading = polynomial.leadingCoeff := by
  have associatedProduct :=
    bivariatePrimeFactors_product_associated polynomial polynomialNeZero
  have factorDvd : factor ∣ polynomial :=
    (Multiset.dvd_prod factorMem).trans associatedProduct.dvd
  obtain ⟨quotient, quotientEquation⟩ := factorDvd
  have factorNeZero : factor ≠ 0 :=
    (bivariatePrimeFactors_prime polynomial polynomialNeZero factor
      factorMem).ne_zero
  have quotientNeZero : quotient ≠ 0 := by
    intro quotientZero
    rw [quotientZero, mul_zero] at quotientEquation
    exact polynomialNeZero quotientEquation
  have quotientLeadingNeZero : quotient.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr quotientNeZero
  refine ⟨quotient.leadingCoeff, quotientLeadingNeZero, ?_⟩
  rw [quotientEquation, Polynomial.leadingCoeff_mul]

/-- Exact `Z`-degree accounting for the leading-coefficient quotient. -/
theorem leadingCoeff_quotient_natDegree_add
    {K : Type*} [Field K]
    (factorLeading quotientLeading parentLeading : Polynomial K)
    (factorLeadingNeZero : factorLeading ≠ 0)
    (quotientLeadingNeZero : quotientLeading ≠ 0)
    (equation : factorLeading * quotientLeading = parentLeading) :
    factorLeading.natDegree + quotientLeading.natDegree =
      parentLeading.natDegree := by
  rw [← equation, Polynomial.natDegree_mul factorLeadingNeZero
    quotientLeadingNeZero]

noncomputable def positiveYBivariatePrimeFactors
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K) :
    Multiset (BivariatePolynomial K) :=
  (bivariatePrimeFactors polynomial).filter
    (fun factor => 0 < factor.natDegree)

@[simp] theorem mem_positiveYBivariatePrimeFactors
    {K : Type*} [Field K]
    (polynomial factor : BivariatePolynomial K) :
    factor ∈ positiveYBivariatePrimeFactors polynomial ↔
      factor ∈ bivariatePrimeFactors polynomial ∧ 0 < factor.natDegree := by
  classical
  simp [positiveYBivariatePrimeFactors]

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

/-- The fixed local factor family has at most the parent's `Y` degree many
positive-degree branches. -/
theorem positiveYBivariatePrimeFactors_card_le_natDegree
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0) :
    (positiveYBivariatePrimeFactors polynomial).card ≤
      polynomial.natDegree := by
  classical
  let factors := bivariatePrimeFactors polynomial
  have factorsPrime : ∀ factor ∈ factors, Prime factor :=
    bivariatePrimeFactors_prime polynomial polynomialNeZero
  have zeroNotMem : (0 : BivariatePolynomial K) ∉ factors := by
    intro zeroMem
    exact (factorsPrime 0 zeroMem).ne_zero rfl
  have productDegree : factors.prod.natDegree =
      (factors.map Polynomial.natDegree).sum :=
    Polynomial.natDegree_multiset_prod factors zeroNotMem
  have associatedProduct : Associated factors.prod polynomial :=
    bivariatePrimeFactors_product_associated polynomial polynomialNeZero
  have degreeEquality : factors.prod.natDegree = polynomial.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated associatedProduct)
  calc
    (positiveYBivariatePrimeFactors polynomial).card =
        (factors.filter (fun factor => 0 < factor.natDegree)).card := rfl
    _ ≤ (factors.map Polynomial.natDegree).sum :=
      card_filter_positive_le_sum_map factors Polynomial.natDegree
    _ = factors.prod.natDegree := productDegree.symm
    _ = polynomial.natDegree := degreeEquality

/-- Additive local-branch degree bound, retaining factor multiplicity. -/
theorem sum_positiveYBivariatePrimeFactors_natDegree_le
    {K : Type*} [Field K] (polynomial : BivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0) :
    ((positiveYBivariatePrimeFactors polynomial).map
        Polynomial.natDegree).sum ≤ polynomial.natDegree := by
  classical
  let factors := bivariatePrimeFactors polynomial
  have factorsPrime : ∀ factor ∈ factors, Prime factor :=
    bivariatePrimeFactors_prime polynomial polynomialNeZero
  have zeroNotMem : (0 : BivariatePolynomial K) ∉ factors := by
    intro zeroMem
    exact (factorsPrime 0 zeroMem).ne_zero rfl
  have productDegree : factors.prod.natDegree =
      (factors.map Polynomial.natDegree).sum :=
    Polynomial.natDegree_multiset_prod factors zeroNotMem
  have associatedProduct : Associated factors.prod polynomial :=
    bivariatePrimeFactors_product_associated polynomial polynomialNeZero
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

/-- Specialize the local factor's challenge variable `Z`. -/
def specializeLocalChallenge
    {K : Type*} [Field K] (z : K) :
    BivariatePolynomial K →+* Polynomial K :=
  Polynomial.mapRingHom (Polynomial.evalRingHom z)

/-- Evaluate a local `Y,Z` factor at the challenge and candidate scalar. -/
def localChallengeCandidateHom
    {K : Type*} [Field K] (z candidate : K) :
    BivariatePolynomial K →+* K :=
  (Polynomial.evalRingHom candidate).comp (specializeLocalChallenge z)

/-- A root of a nonzero local specialization is carried by one positive-
`Y`-degree member of the fixed local prime factorization. -/
theorem exists_positiveDegree_bivariatePrimeFactor_root
    {K : Type*} [Field K]
    (polynomial : BivariatePolynomial K)
    (polynomialNeZero : polynomial ≠ 0)
    (z candidate : K)
    (specializationNeZero : specializeLocalChallenge z polynomial ≠ 0)
    (candidateRoot : localChallengeCandidateHom z candidate polynomial = 0) :
    ∃ factor ∈ bivariatePrimeFactors polynomial,
      0 < factor.natDegree ∧
        localChallengeCandidateHom z candidate factor = 0 := by
  classical
  let factors := bivariatePrimeFactors polynomial
  have associatedProduct : Associated factors.prod polynomial :=
    bivariatePrimeFactors_product_associated polynomial polynomialNeZero
  have mappedAssociated := associatedProduct.map
    (localChallengeCandidateHom z candidate)
  have mappedProductZero :
      (factors.map (localChallengeCandidateHom z candidate)).prod = 0 := by
    rw [← map_multiset_prod]
    exact mappedAssociated.eq_zero_iff.mpr candidateRoot
  have zeroMem : (0 : K) ∈
      factors.map (localChallengeCandidateHom z candidate) :=
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
  have specializedFactorZero : specializeLocalChallenge z factor = 0 := by
    rw [factorConstant] at factorRoot ⊢
    simpa [localChallengeCandidateHom, specializeLocalChallenge,
      coe_evalRingHom] using factorRoot
  have specializedDvd : specializeLocalChallenge z factor ∣
      specializeLocalChallenge z polynomial := _root_.map_dvd _ factorDvd
  rw [specializedFactorZero, zero_dvd_iff] at specializedDvd
  exact specializationNeZero specializedDvd

/-- The explicit simple-root predicate guarantees that the local specialized
parent is nonzero. -/
theorem localSpecialization_ne_zero_of_simpleSpecializedRoot
    {K : Type*} [Field K]
    (globalFactor : TrivariatePolynomial K) (x z : K) (candidate : K[X])
    (simple : SimpleSpecializedRoot globalFactor x z candidate) :
    specializeLocalChallenge z
      (specializeEvaluationPoint x globalFactor) ≠ 0 := by
  intro specializationZero
  apply simple.2
  rw [← specializeEvaluationPointChallenge_derivative]
  rw [IsRoot]
  change (specializeEvaluationPointChallenge x z
    globalFactor.derivative).eval (candidate.eval x) = 0
  have derivativeZero : specializeEvaluationPointChallenge x z
      globalFactor.derivative = 0 := by
    rw [specializeEvaluationPointChallenge_derivative]
    change (specializeLocalChallenge z
      (specializeEvaluationPoint x globalFactor)).derivative = 0
    rw [specializationZero, derivative_zero]
  rw [derivativeZero, eval_zero]

/-- A simple challenge root is assigned to one member of the fixed local
factorization of `R(x₀,Y,Z)`. -/
theorem exists_localPrimeFactor_for_simpleSpecializedRoot
    {K : Type*} [Field K]
    (globalFactor : TrivariatePolynomial K) (x z : K) (candidate : K[X])
    (localPolynomialNeZero : specializeEvaluationPoint x globalFactor ≠ 0)
    (simple : SimpleSpecializedRoot globalFactor x z candidate) :
    ∃ localFactor ∈ bivariatePrimeFactors
        (specializeEvaluationPoint x globalFactor),
      0 < localFactor.natDegree ∧
        localChallengeCandidateHom z (candidate.eval x) localFactor = 0 := by
  apply exists_positiveDegree_bivariatePrimeFactor_root
    (specializeEvaluationPoint x globalFactor) localPolynomialNeZero z
    (candidate.eval x)
    (localSpecialization_ne_zero_of_simpleSpecializedRoot
      globalFactor x z candidate simple)
  exact simple.1

/-- Pigeonhole the independently selected simple roots into one correct,
fixed irreducible local branch `H(Y,Z)`. -/
theorem exists_frequent_localPrimeFactor
    {K : Type*} [Field K] [DecidableEq K]
    (globalFactor : TrivariatePolynomial K) (x : K)
    (candidate : K → K[X]) (challenges : Finset K) (branchTarget : Nat)
    (localPolynomialNeZero : specializeEvaluationPoint x globalFactor ≠ 0)
    (simple : ∀ z ∈ challenges,
      SimpleSpecializedRoot globalFactor x z (candidate z))
    (many : (specializeEvaluationPoint x globalFactor).natDegree *
      branchTarget < challenges.card) :
    ∃ localFactor ∈ bivariatePrimeFactors
        (specializeEvaluationPoint x globalFactor),
      0 < localFactor.natDegree ∧ branchTarget <
        (challenges.filter fun z =>
          localChallengeCandidateHom z ((candidate z).eval x)
            localFactor = 0).card := by
  classical
  let polynomial := specializeEvaluationPoint x globalFactor
  have branchExists : ∀ z ∈ challenges,
      ∃ factor ∈ positiveYBivariatePrimeFactors polynomial,
        localChallengeCandidateHom z ((candidate z).eval x) factor = 0 := by
    intro z zMem
    obtain ⟨factor, factorMem, factorDegree, factorRoot⟩ :=
      exists_localPrimeFactor_for_simpleSpecializedRoot globalFactor x z
        (candidate z) localPolynomialNeZero (simple z zMem)
    exact ⟨factor,
      (mem_positiveYBivariatePrimeFactors polynomial factor).mpr
        ⟨factorMem, factorDegree⟩,
      factorRoot⟩
  let selectedFactor : K → BivariatePolynomial K := fun z =>
    if zMem : z ∈ challenges then Classical.choose (branchExists z zMem)
    else polynomial
  have selectedFactorSpec : ∀ z ∈ challenges,
      selectedFactor z ∈ positiveYBivariatePrimeFactors polynomial ∧
        localChallengeCandidateHom z ((candidate z).eval x)
          (selectedFactor z) = 0 := by
    intro z zMem
    simp only [selectedFactor, dif_pos zMem]
    exact Classical.choose_spec (branchExists z zMem)
  let branches := (positiveYBivariatePrimeFactors polynomial).toFinset
  have selectedMaps : ∀ z ∈ challenges, selectedFactor z ∈ branches := by
    intro z zMem
    simpa only [branches, Multiset.mem_toFinset] using
      (selectedFactorSpec z zMem).1
  have branchCardLe : branches.card ≤ polynomial.natDegree :=
    (Multiset.toFinset_card_le
      (positiveYBivariatePrimeFactors polynomial)).trans
      (positiveYBivariatePrimeFactors_card_le_natDegree polynomial
        localPolynomialNeZero)
  have enoughForPigeonhole : branches.card * branchTarget < challenges.card :=
    (Nat.mul_le_mul_right branchTarget branchCardLe).trans_lt many
  obtain ⟨factor, factorMem, frequentFiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := challenges) (t := branches) (f := selectedFactor)
      selectedMaps enoughForPigeonhole
  have factorPositiveMem : factor ∈
      positiveYBivariatePrimeFactors polynomial := by
    simpa only [branches, Multiset.mem_toFinset] using factorMem
  have fiberSubset :
      challenges.filter (fun z => selectedFactor z = factor) ⊆
        challenges.filter (fun z =>
          localChallengeCandidateHom z ((candidate z).eval x) factor = 0) := by
    intro z zMem
    rw [Finset.mem_filter] at zMem ⊢
    refine ⟨zMem.1, ?_⟩
    rw [← zMem.2]
    exact (selectedFactorSpec z zMem.1).2
  have frequentRoots : branchTarget <
      (challenges.filter fun z =>
        localChallengeCandidateHom z ((candidate z).eval x) factor = 0).card :=
    frequentFiber.trans_le (Finset.card_le_card fiberSubset)
  exact ⟨factor,
    (mem_positiveYBivariatePrimeFactors polynomial factor).mp
      factorPositiveMem |>.1,
    (mem_positiveYBivariatePrimeFactors polynomial factor).mp
      factorPositiveMem |>.2,
    frequentRoots⟩

#print axioms bivariatePrimeFactors_product_associated
#print axioms exists_leadingCoeff_quotient_of_bivariatePrimeFactor
#print axioms leadingCoeff_quotient_natDegree_add
#print axioms positiveYBivariatePrimeFactors_card_le_natDegree
#print axioms sum_positiveYBivariatePrimeFactors_natDegree_le
#print axioms exists_localPrimeFactor_for_simpleSpecializedRoot
#print axioms exists_frequent_localPrimeFactor

end

end AspisK1.V7ExactCorrelatedAgreementLocalFactors
