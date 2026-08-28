import AspisFormal.K1.V7ExactCorrelatedAgreementPowerSeriesLift
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Algebraic weights for the exact local function-field argument

BCIKS Appendix A assigns weight `1` to the challenge variable `Z` and a
branch-dependent weight to the integral generator `T`.  This file defines
that weight on the literal bivariate polynomial representation and proves the
subadditivity laws used in the Hensel numerator recurrence.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementRegularWeights

open Polynomial
open scoped Polynomial.Bivariate
open scoped Pointwise
open AspisK1.V7ExactCorrelatedAgreementFactors

noncomputable section

/-- Weight vector `(weight Z, weight T) = (1,tWeight)`. -/
def localWeightVector (tWeight : Nat) : Fin 2 → Nat := ![1, tWeight]

/-- Weighted total degree of a polynomial in inner `Z` and outer `T`. -/
def localBivariateWeight
    {K : Type*} [CommSemiring K] (tWeight : Nat)
    (polynomial : BivariatePolynomial K) : Nat :=
  (Polynomial.Bivariate.equivMvPolynomial K polynomial).weightedTotalDegree
    (localWeightVector tWeight)

@[simp] theorem localBivariateWeight_zero
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight : Nat) :
    localBivariateWeight tWeight (0 : BivariatePolynomial K) = 0 := by
  simpa [localBivariateWeight] using
    (MvPolynomial.weightedTotalDegree_zero
      (R := K) (localWeightVector tWeight))

@[simp] theorem localBivariateWeight_challenge
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight : Nat) :
    localBivariateWeight tWeight
      (C X : BivariatePolynomial K) = 1 := by
  simp [localBivariateWeight, localWeightVector,
    MvPolynomial.weightedTotalDegree, MvPolynomial.support_X,
    Finsupp.weight_single]

@[simp] theorem localBivariateWeight_generator
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight : Nat) :
    localBivariateWeight tWeight
      (X : BivariatePolynomial K) = tWeight := by
  simp [localBivariateWeight, localWeightVector,
    MvPolynomial.weightedTotalDegree, MvPolynomial.support_X,
    Finsupp.weight_single]

@[simp] theorem localBivariateWeight_constant
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight : Nat) (value : K) :
    localBivariateWeight tWeight
      (C (C value) : BivariatePolynomial K) = 0 := by
  by_cases valueZero : value = 0
  · simp [valueZero]
  · simp [localBivariateWeight, localWeightVector,
      MvPolynomial.weightedTotalDegree, Finsupp.weight_apply, valueZero]

/-- Weight is submaximal under addition. -/
theorem localBivariateWeight_add_le
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight : Nat)
    (left right : BivariatePolynomial K) :
    localBivariateWeight tWeight (left + right) ≤
      max (localBivariateWeight tWeight left)
        (localBivariateWeight tWeight right) := by
  classical
  simp only [localBivariateWeight, map_add]
  let weight := localWeightVector tWeight
  let leftMv := Polynomial.Bivariate.equivMvPolynomial K left
  let rightMv := Polynomial.Bivariate.equivMvPolynomial K right
  change (leftMv + rightMv).weightedTotalDegree weight ≤
    max (leftMv.weightedTotalDegree weight)
      (rightMv.weightedTotalDegree weight)
  unfold MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro monomial monomialMem
  have supportMem : monomial ∈ leftMv.support ∪ rightMv.support :=
    MvPolynomial.support_add monomialMem
  rw [Finset.mem_union] at supportMem
  rcases supportMem with leftMem | rightMem
  · exact (MvPolynomial.le_weightedTotalDegree weight leftMem).trans
      (Nat.le_max_left _ _)
  · exact (MvPolynomial.le_weightedTotalDegree weight rightMem).trans
      (Nat.le_max_right _ _)

/-- Weight is subadditive under multiplication.  The proof follows actual
monomial support decomposition, so cancellation cannot invalidate it. -/
theorem localBivariateWeight_mul_le
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight : Nat)
    (left right : BivariatePolynomial K) :
    localBivariateWeight tWeight (left * right) ≤
      localBivariateWeight tWeight left +
        localBivariateWeight tWeight right := by
  classical
  simp only [localBivariateWeight, map_mul]
  let weight := localWeightVector tWeight
  let leftMv := Polynomial.Bivariate.equivMvPolynomial K left
  let rightMv := Polynomial.Bivariate.equivMvPolynomial K right
  change (leftMv * rightMv).weightedTotalDegree weight ≤
    leftMv.weightedTotalDegree weight + rightMv.weightedTotalDegree weight
  unfold MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro monomial monomialMem
  have supportMem : monomial ∈ leftMv.support + rightMv.support :=
    MvPolynomial.support_mul leftMv rightMv monomialMem
  rw [Finset.mem_add] at supportMem
  obtain ⟨leftMonomial, leftMem, rightMonomial, rightMem, decomposition⟩ :=
    supportMem
  rw [← decomposition, map_add]
  exact Nat.add_le_add
    (MvPolynomial.le_weightedTotalDegree weight leftMem)
    (MvPolynomial.le_weightedTotalDegree weight rightMem)

/-! ## Exact multiplicativity for nonzero factors -/

/-- The homogeneous component at the weighted total degree of a nonzero
multivariate polynomial is nonzero. -/
theorem weightedHomogeneousComponent_top_ne_zero
    {K σ : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (weight : σ → Nat) (polynomial : MvPolynomial σ K)
    (polynomialNeZero : polynomial ≠ 0) :
    MvPolynomial.weightedHomogeneousComponent weight
        (polynomial.weightedTotalDegree weight) polynomial ≠ 0 := by
  classical
  have supportNonempty : polynomial.support.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr <| by
      intro supportEmpty
      apply polynomialNeZero
      exact MvPolynomial.support_eq_empty.mp supportEmpty
  obtain ⟨monomial, monomialMem, topWeight⟩ :=
    Finset.exists_mem_eq_sup polynomial.support supportNonempty
      (Finsupp.weight weight)
  intro componentZero
  have coefficientZero := congrArg (MvPolynomial.coeff monomial) componentZero
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at coefficientZero
  have weightEquality : Finsupp.weight weight monomial =
      polynomial.weightedTotalDegree weight := by
    exact topWeight.symm
  rw [if_pos weightEquality] at coefficientZero
  exact (MvPolynomial.mem_support_iff.mp monomialMem) coefficientZero

/-- The top component of a product is exactly the product of the two top
components.  This is the cancellation-safe fact omitted by a mere support
upper bound. -/
theorem weightedHomogeneousComponent_mul_top
    {K σ : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (weight : σ → Nat) (left right : MvPolynomial σ K) :
    MvPolynomial.weightedHomogeneousComponent weight
        (left.weightedTotalDegree weight + right.weightedTotalDegree weight)
        (left * right) =
      MvPolynomial.weightedHomogeneousComponent weight
          (left.weightedTotalDegree weight) left *
        MvPolynomial.weightedHomogeneousComponent weight
          (right.weightedTotalDegree weight) right := by
  classical
  let leftDegree := left.weightedTotalDegree weight
  let rightDegree := right.weightedTotalDegree weight
  ext monomial
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  simp_rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases totalWeight : Finsupp.weight weight monomial =
      leftDegree + rightDegree
  · rw [if_pos totalWeight]
    apply Finset.sum_congr rfl
    intro pair pairMem
    have decomposition : pair.1 + pair.2 = monomial :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp pairMem
    by_cases leftCoefficient : MvPolynomial.coeff pair.1 left = 0
    · simp [leftCoefficient]
    by_cases rightCoefficient : MvPolynomial.coeff pair.2 right = 0
    · simp [rightCoefficient]
    have leftMem : pair.1 ∈ left.support :=
      MvPolynomial.mem_support_iff.mpr leftCoefficient
    have rightMem : pair.2 ∈ right.support :=
      MvPolynomial.mem_support_iff.mpr rightCoefficient
    have leftLe : Finsupp.weight weight pair.1 ≤ leftDegree :=
      MvPolynomial.le_weightedTotalDegree weight leftMem
    have rightLe : Finsupp.weight weight pair.2 ≤ rightDegree :=
      MvPolynomial.le_weightedTotalDegree weight rightMem
    have weightSum : Finsupp.weight weight pair.1 +
        Finsupp.weight weight pair.2 = leftDegree + rightDegree := by
      calc
        Finsupp.weight weight pair.1 + Finsupp.weight weight pair.2 =
            Finsupp.weight weight monomial := by
          rw [← decomposition, map_add]
        _ = leftDegree + rightDegree := totalWeight
    have leftEqual : Finsupp.weight weight pair.1 = leftDegree := by omega
    have rightEqual : Finsupp.weight weight pair.2 = rightDegree := by omega
    simp [leftEqual, rightEqual, leftDegree, rightDegree]
  · rw [if_neg totalWeight]
    symm
    apply Finset.sum_eq_zero
    intro pair pairMem
    have decomposition : pair.1 + pair.2 = monomial :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp pairMem
    by_cases leftEqual : Finsupp.weight weight pair.1 = leftDegree
    · by_cases rightEqual : Finsupp.weight weight pair.2 = rightDegree
      · exfalso
        apply totalWeight
        calc
          Finsupp.weight weight monomial =
              Finsupp.weight weight (pair.1 + pair.2) := by rw [decomposition]
          _ = Finsupp.weight weight pair.1 +
              Finsupp.weight weight pair.2 := by rw [map_add]
          _ = leftDegree + rightDegree := by rw [leftEqual, rightEqual]
      · simp [leftEqual, rightEqual, leftDegree, rightDegree]
    · simp [leftEqual, leftDegree]

/-- Weighted total degree is additive on nonzero products over a field. -/
theorem weightedTotalDegree_mul_eq
    {K σ : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (weight : σ → Nat) (left right : MvPolynomial σ K)
    (leftNeZero : left ≠ 0) (rightNeZero : right ≠ 0) :
    (left * right).weightedTotalDegree weight =
      left.weightedTotalDegree weight + right.weightedTotalDegree weight := by
  classical
  apply le_antisymm
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro monomial monomialMem
    have supportMem : monomial ∈ left.support + right.support :=
      MvPolynomial.support_mul left right monomialMem
    rw [Finset.mem_add] at supportMem
    obtain ⟨leftMonomial, leftMem, rightMonomial, rightMem,
      decomposition⟩ := supportMem
    rw [← decomposition, map_add]
    exact Nat.add_le_add
      (MvPolynomial.le_weightedTotalDegree weight leftMem)
      (MvPolynomial.le_weightedTotalDegree weight rightMem)
  · by_contra degreeNotLe
    have degreeLt : (left * right).weightedTotalDegree weight <
        left.weightedTotalDegree weight + right.weightedTotalDegree weight :=
      Nat.lt_of_not_ge degreeNotLe
    have topZero := MvPolynomial.weightedHomogeneousComponent_eq_zero
      (φ := left * right)
      (n := left.weightedTotalDegree weight + right.weightedTotalDegree weight)
      degreeLt
    rw [weightedHomogeneousComponent_mul_top weight left right] at topZero
    exact (mul_ne_zero
      (weightedHomogeneousComponent_top_ne_zero weight left leftNeZero)
      (weightedHomogeneousComponent_top_ne_zero weight right rightNeZero))
      topZero

/-- Consequently the concrete bivariate weight used for V7 is exactly
additive on nonzero products. -/
theorem localBivariateWeight_mul_eq
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K] (tWeight : Nat)
    (left right : BivariatePolynomial K)
    (leftNeZero : left ≠ 0) (rightNeZero : right ≠ 0) :
    localBivariateWeight tWeight (left * right) =
      localBivariateWeight tWeight left +
        localBivariateWeight tWeight right := by
  simp only [localBivariateWeight, map_mul]
  apply weightedTotalDegree_mul_eq
  · simpa only [map_zero] using
      (Polynomial.Bivariate.equivMvPolynomial K).injective.ne leftNeZero
  · simpa only [map_zero] using
      (Polynomial.Bivariate.equivMvPolynomial K).injective.ne rightNeZero

/-- Exact additivity over a finite nonzero factor multiset.  This is the
form used by the improved BCH+25 branch budget: every irreducible factor is
charged its own weight, rather than the parent's worst-case weight. -/
theorem localBivariateWeight_multiset_prod_eq
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K] (tWeight : Nat)
    (factors : Multiset (BivariatePolynomial K))
    (zeroNotMem : (0 : BivariatePolynomial K) ∉ factors) :
    localBivariateWeight tWeight factors.prod =
      (factors.map (localBivariateWeight tWeight)).sum := by
  induction factors using Multiset.induction_on with
  | empty =>
      simp [localBivariateWeight, MvPolynomial.weightedTotalDegree,
        MvPolynomial.support_one]
  | @cons factor factors induction =>
      have factorNeZero : factor ≠ 0 := by
        intro factorZero
        apply zeroNotMem
        simp [factorZero]
      have zeroNotMemTail : (0 : BivariatePolynomial K) ∉ factors := by
        intro zeroMem
        exact zeroNotMem (Multiset.mem_cons_of_mem zeroMem)
      have productNeZero : factors.prod ≠ 0 :=
        Multiset.prod_ne_zero zeroNotMemTail
      simp only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      rw [localBivariateWeight_mul_eq tWeight factor factors.prod
        factorNeZero productNeZero, induction zeroNotMemTail]

/-- Multiplication by a power costs at most the corresponding multiple of
the factor's weight. -/
theorem localBivariateWeight_pow_le
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight : Nat)
    (polynomial : BivariatePolynomial K) (exponent : Nat) :
    localBivariateWeight tWeight (polynomial ^ exponent) ≤
      exponent * localBivariateWeight tWeight polynomial := by
  induction exponent with
  | zero => simp [localBivariateWeight, MvPolynomial.weightedTotalDegree]
  | succ exponent induction =>
    rw [pow_succ]
    exact (localBivariateWeight_mul_le tWeight _ _).trans <| by
      calc
        localBivariateWeight tWeight (polynomial ^ exponent) +
            localBivariateWeight tWeight polynomial ≤
            exponent * localBivariateWeight tWeight polynomial +
              localBivariateWeight tWeight polynomial :=
          Nat.add_le_add_right induction _
        _ = (exponent + 1) * localBivariateWeight tWeight polynomial := by
          rw [Nat.succ_mul]

/-- A finite sum has bounded weight when every summand has that bound. -/
theorem localBivariateWeight_finset_sum_le
    {K ι : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight bound : Nat)
    (indices : Finset ι) (term : ι → BivariatePolynomial K)
    (termBound : ∀ index ∈ indices,
      localBivariateWeight tWeight (term index) ≤ bound) :
    localBivariateWeight tWeight (∑ index ∈ indices, term index) ≤
      bound := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices indexNotMem induction =>
      rw [Finset.sum_insert indexNotMem]
      exact (localBivariateWeight_add_le tWeight _ _).trans <|
        max_le (termBound index (Finset.mem_insert_self index indices))
          (induction fun other otherMem ↦
            termBound other (Finset.mem_insert_of_mem otherMem))

/-- An inner coefficient polynomial, embedded as an outer constant, costs
at most its ordinary degree in the challenge variable. -/
theorem localBivariateWeight_C_le_natDegree
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight : Nat) (coefficient : Polynomial K) :
    localBivariateWeight tWeight (C coefficient) ≤ coefficient.natDegree := by
  classical
  calc
    localBivariateWeight tWeight (C coefficient) =
        localBivariateWeight tWeight
          (∑ exponent ∈ coefficient.support,
            C (Polynomial.monomial exponent (coefficient.coeff exponent))) := by
      rw [← map_sum, ← coefficient.as_sum_support]
    _ ≤ coefficient.natDegree := by
      apply localBivariateWeight_finset_sum_le tWeight coefficient.natDegree
      intro exponent exponentMem
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      calc
        localBivariateWeight tWeight
            (C (C (coefficient.coeff exponent)) * C X ^ exponent) ≤
            localBivariateWeight tWeight
                (C (C (coefficient.coeff exponent))) +
              localBivariateWeight tWeight (C X ^ exponent) :=
          localBivariateWeight_mul_le tWeight _ _
        _ ≤ 0 + exponent * 1 := Nat.add_le_add
          (le_of_eq (localBivariateWeight_constant tWeight _))
          (by simpa using
            (localBivariateWeight_pow_le tWeight
              (C X : BivariatePolynomial K) exponent))
        _ = exponent := by omega
        _ ≤ coefficient.natDegree :=
          Polynomial.le_natDegree_of_mem_supp exponent exponentMem

/-- Weight bound for one outer monomial `coefficient * T^exponent`. -/
theorem localBivariateWeight_monomial_le
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight exponent : Nat)
    (coefficient : Polynomial K) :
    localBivariateWeight tWeight (Polynomial.monomial exponent coefficient) ≤
      coefficient.natDegree + exponent * tWeight := by
  rw [← C_mul_X_pow_eq_monomial]
  exact (localBivariateWeight_mul_le tWeight _ _).trans <| by
    gcongr
    · exact localBivariateWeight_C_le_natDegree tWeight coefficient
    · exact (localBivariateWeight_pow_le tWeight X exponent).trans_eq <| by
        simp

/-- Coefficientwise bounds imply a bound on the whole bivariate polynomial.
This is the form used for the monicized local equation and Hensel
numerators. -/
theorem localBivariateWeight_le_of_coeff
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight bound : Nat)
    (polynomial : BivariatePolynomial K)
    (coefficientBound : ∀ exponent ∈ polynomial.support,
      (polynomial.coeff exponent).natDegree + exponent * tWeight ≤ bound) :
    localBivariateWeight tWeight polynomial ≤ bound := by
  classical
  rw [polynomial.as_sum_support]
  apply localBivariateWeight_finset_sum_le tWeight bound
  intro exponent exponentMem
  exact (localBivariateWeight_monomial_le tWeight exponent
    (polynomial.coeff exponent)).trans
      (coefficientBound exponent exponentMem)

/-! ## Equivalent iterated-support presentation

For division by the monicized local equation it is useful to expose the
coefficient formula directly.  This is the same algebraic weight, presented
as the supremum of `deg_Z(coefficient_j) + j * weight(T)`.  The following
lemmas prove its ring laws without assuming that specialization preserves
degree.
-/

def iteratedBivariateWeight
    {K : Type*} [Field K] (tWeight : Nat)
    (polynomial : BivariatePolynomial K) : Nat :=
  polynomial.support.sup fun exponent =>
    (polynomial.coeff exponent).natDegree + exponent * tWeight

@[simp] theorem iteratedBivariateWeight_zero
    {K : Type*} [Field K] (tWeight : Nat) :
    iteratedBivariateWeight tWeight (0 : BivariatePolynomial K) = 0 := by
  simp [iteratedBivariateWeight]

@[simp] theorem iteratedBivariateWeight_neg
    {K : Type*} [Field K] (tWeight : Nat)
    (polynomial : BivariatePolynomial K) :
    iteratedBivariateWeight tWeight (-polynomial) =
      iteratedBivariateWeight tWeight polynomial := by
  simp [iteratedBivariateWeight]

/-- A single outer monomial has at most its evident coefficient-plus-generator
weight.  Equality is unnecessary for the division invariant. -/
theorem iteratedBivariateWeight_monomial_le
    {K : Type*} [Field K] (tWeight exponent : Nat)
    (coefficient : Polynomial K) :
    iteratedBivariateWeight tWeight
        (Polynomial.monomial exponent coefficient) ≤
      coefficient.natDegree + exponent * tWeight := by
  classical
  by_cases coefficientZero : coefficient = 0
  · simp [coefficientZero]
  · simp [iteratedBivariateWeight, Polynomial.support_monomial,
      coefficientZero]

/-- Every nonzero outer coefficient contributes its literal weighted
degree to the supremum. -/
theorem coeff_weight_le_iteratedBivariateWeight
    {K : Type*} [Field K] (tWeight : Nat)
    (polynomial : BivariatePolynomial K) (exponent : Nat)
    (coefficientMem : exponent ∈ polynomial.support) :
    (polynomial.coeff exponent).natDegree + exponent * tWeight ≤
      iteratedBivariateWeight tWeight polynomial := by
  exact Finset.le_sup
    (s := polynomial.support)
    (f := fun index : Nat =>
      (polynomial.coeff index).natDegree + index * tWeight)
    coefficientMem

/-- A coefficientwise ceiling bounds the iterated-support weight. -/
theorem iteratedBivariateWeight_le_of_coeff
    {K : Type*} [Field K] (tWeight bound : Nat)
    (polynomial : BivariatePolynomial K)
    (coefficientBound : ∀ exponent ∈ polynomial.support,
      (polynomial.coeff exponent).natDegree + exponent * tWeight ≤ bound) :
    iteratedBivariateWeight tWeight polynomial ≤ bound := by
  unfold iteratedBivariateWeight
  exact Finset.sup_le coefficientBound

/-- Iterated weight is submaximal under addition. -/
theorem iteratedBivariateWeight_add_le
    {K : Type*} [Field K] (tWeight : Nat)
    (left right : BivariatePolynomial K) :
    iteratedBivariateWeight tWeight (left + right) ≤
      max (iteratedBivariateWeight tWeight left)
        (iteratedBivariateWeight tWeight right) := by
  classical
  change ((left + right).support.sup fun exponent =>
      ((left + right).coeff exponent).natDegree + exponent * tWeight) ≤ _
  apply Finset.sup_le
  intro exponent exponentMem
  have unionMem : exponent ∈ left.support ∪ right.support :=
    Polynomial.support_add exponentMem
  rw [Finset.mem_union] at unionMem
  have leftBound : (left.coeff exponent).natDegree + exponent * tWeight ≤
      max (iteratedBivariateWeight tWeight left)
        (iteratedBivariateWeight tWeight right) := by
    rcases unionMem with leftMem | rightMem
    · exact (coeff_weight_le_iteratedBivariateWeight tWeight left
        exponent leftMem).trans (Nat.le_max_left _ _)
    · by_cases leftMem : exponent ∈ left.support
      · exact (coeff_weight_le_iteratedBivariateWeight tWeight left
          exponent leftMem).trans (Nat.le_max_left _ _)
      · have leftCoefficientZero : left.coeff exponent = 0 := by
          by_contra nonzero
          exact leftMem (Polynomial.mem_support_iff.mpr nonzero)
        rw [leftCoefficientZero, Polynomial.natDegree_zero, zero_add]
        exact (Nat.le_add_left _ _).trans <|
          (coeff_weight_le_iteratedBivariateWeight tWeight right
            exponent rightMem).trans (Nat.le_max_right _ _)
  have rightBound : (right.coeff exponent).natDegree + exponent * tWeight ≤
      max (iteratedBivariateWeight tWeight left)
        (iteratedBivariateWeight tWeight right) := by
    rcases unionMem with leftMem | rightMem
    · by_cases rightMem : exponent ∈ right.support
      · exact (coeff_weight_le_iteratedBivariateWeight tWeight right
          exponent rightMem).trans (Nat.le_max_right _ _)
      · have rightCoefficientZero : right.coeff exponent = 0 := by
          by_contra nonzero
          exact rightMem (Polynomial.mem_support_iff.mpr nonzero)
        rw [rightCoefficientZero, Polynomial.natDegree_zero, zero_add]
        exact (Nat.le_add_left _ _).trans <|
          (coeff_weight_le_iteratedBivariateWeight tWeight left
            exponent leftMem).trans (Nat.le_max_left _ _)
    · exact (coeff_weight_le_iteratedBivariateWeight tWeight right
        exponent rightMem).trans (Nat.le_max_right _ _)
  rw [Polynomial.coeff_add]
  have degreeBound :
      (left.coeff exponent + right.coeff exponent).natDegree ≤
        max (left.coeff exponent).natDegree
          (right.coeff exponent).natDegree :=
    Polynomial.natDegree_add_le (left.coeff exponent) (right.coeff exponent)
  calc
    (left.coeff exponent + right.coeff exponent).natDegree +
        exponent * tWeight ≤
        max (left.coeff exponent).natDegree
            (right.coeff exponent).natDegree + exponent * tWeight :=
      Nat.add_le_add_right degreeBound _
    _ = max ((left.coeff exponent).natDegree + exponent * tWeight)
        ((right.coeff exponent).natDegree + exponent * tWeight) := by
      omega
    _ ≤ max (iteratedBivariateWeight tWeight left)
        (iteratedBivariateWeight tWeight right) :=
      max_le leftBound rightBound

/-- Iterated weight is subadditive under multiplication.  The proof uses an
actual nonzero convolution term to control the outer exponent, and separately
bounds every coefficient term; zero summands do not create a false support
witness. -/
theorem iteratedBivariateWeight_mul_le
    {K : Type*} [Field K] (tWeight : Nat)
    (left right : BivariatePolynomial K) :
    iteratedBivariateWeight tWeight (left * right) ≤
      iteratedBivariateWeight tWeight left +
        iteratedBivariateWeight tWeight right := by
  classical
  let budget := iteratedBivariateWeight tWeight left +
    iteratedBivariateWeight tWeight right
  unfold iteratedBivariateWeight
  apply Finset.sup_le
  intro exponent exponentMem
  have coefficientNeZero : (left * right).coeff exponent ≠ 0 :=
    Polynomial.mem_support_iff.mp exponentMem
  rw [Polynomial.coeff_mul] at coefficientNeZero
  obtain ⟨witness, witnessMem, witnessNeZero⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero coefficientNeZero
  have witnessSum : witness.1 + witness.2 = exponent :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp witnessMem
  have leftWitnessNeZero : left.coeff witness.1 ≠ 0 := by
    exact left_ne_zero_of_mul witnessNeZero
  have rightWitnessNeZero : right.coeff witness.2 ≠ 0 := by
    exact right_ne_zero_of_mul witnessNeZero
  have leftWitnessMem : witness.1 ∈ left.support :=
    Polynomial.mem_support_iff.mpr leftWitnessNeZero
  have rightWitnessMem : witness.2 ∈ right.support :=
    Polynomial.mem_support_iff.mpr rightWitnessNeZero
  have exponentWeightLe : exponent * tWeight ≤ budget := by
    have leftLower := coeff_weight_le_iteratedBivariateWeight tWeight left
      witness.1 leftWitnessMem
    have rightLower := coeff_weight_le_iteratedBivariateWeight tWeight right
      witness.2 rightWitnessMem
    dsimp [budget]
    rw [← witnessSum, Nat.add_mul]
    omega
  have coefficientDegreeLe :
      ((left * right).coeff exponent).natDegree ≤
        budget - exponent * tWeight := by
    rw [Polynomial.coeff_mul]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro pair pairMem
    by_cases termZero : left.coeff pair.1 * right.coeff pair.2 = 0
    · rw [termZero, Polynomial.natDegree_zero]
      exact Nat.zero_le _
    · have pairSum : pair.1 + pair.2 = exponent :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp pairMem
      have leftNeZero : left.coeff pair.1 ≠ 0 :=
        left_ne_zero_of_mul termZero
      have rightNeZero : right.coeff pair.2 ≠ 0 :=
        right_ne_zero_of_mul termZero
      have leftMem : pair.1 ∈ left.support :=
        Polynomial.mem_support_iff.mpr leftNeZero
      have rightMem : pair.2 ∈ right.support :=
        Polynomial.mem_support_iff.mpr rightNeZero
      have leftLower := coeff_weight_le_iteratedBivariateWeight tWeight left
        pair.1 leftMem
      have rightLower := coeff_weight_le_iteratedBivariateWeight tWeight right
        pair.2 rightMem
      have termDegree := Polynomial.natDegree_mul_le
        (p := left.coeff pair.1) (q := right.coeff pair.2)
      have termWithExponent :
          (left.coeff pair.1 * right.coeff pair.2).natDegree +
            exponent * tWeight ≤ budget := by
        dsimp [budget]
        rw [← pairSum, Nat.add_mul]
        omega
      omega
  have finalBound : ((left * right).coeff exponent).natDegree +
      exponent * tWeight ≤ budget :=
    add_le_of_le_tsub_right_of_le exponentWeightLe coefficientDegreeLe
  dsimp [budget, iteratedBivariateWeight] at finalBound ⊢
  exact finalBound

-- Unfolding mathlib's well-founded monic division exposes a large recursive
-- term; the extra heartbeat allowance is elaboration-only.
set_option maxHeartbeats 1000000 in
/-- Complete monic division cannot increase iterated weight when the modulus
has weight at most `deg(modulus) * weight(T)`.  This follows the literal
well-founded division implemented by mathlib and checks the weight of every
single leading-term reduction. -/
theorem iteratedBivariateWeight_modByMonic_le
    {K : Type*} [Field K] (tWeight : Nat)
    (modulus : BivariatePolynomial K) (modulusMonic : modulus.Monic)
    (modulusWeight : iteratedBivariateWeight tWeight modulus ≤
      modulus.natDegree * tWeight) :
    ∀ polynomial : BivariatePolynomial K,
      iteratedBivariateWeight tWeight (polynomial %ₘ modulus) ≤
        iteratedBivariateWeight tWeight polynomial
  | polynomial => by
      classical
      if reducible : modulus.degree ≤ polynomial.degree ∧ polynomial ≠ 0 then
        have _wf := Polynomial.div_wf_lemma reducible modulusMonic
        have induction := iteratedBivariateWeight_modByMonic_le tWeight
          modulus modulusMonic modulusWeight
            (polynomial - modulus * (C polynomial.leadingCoeff *
              X ^ (polynomial.natDegree - modulus.natDegree)))
        have modulusDegreeLe : modulus.natDegree ≤ polynomial.natDegree :=
          Polynomial.natDegree_le_natDegree reducible.1
        have leadingMem : polynomial.natDegree ∈ polynomial.support :=
          Polynomial.natDegree_mem_support_of_nonzero reducible.2
        have leadingLower : polynomial.leadingCoeff.natDegree +
            polynomial.natDegree * tWeight ≤
            iteratedBivariateWeight tWeight polynomial := by
          simpa only [Polynomial.leadingCoeff] using
            (coeff_weight_le_iteratedBivariateWeight tWeight polynomial
              polynomial.natDegree leadingMem)
        have reductionMonomialWeight :
            iteratedBivariateWeight tWeight
                (C polynomial.leadingCoeff *
                  X ^ (polynomial.natDegree - modulus.natDegree)) ≤
              polynomial.leadingCoeff.natDegree +
                (polynomial.natDegree - modulus.natDegree) * tWeight := by
          rw [C_mul_X_pow_eq_monomial]
          exact iteratedBivariateWeight_monomial_le tWeight _ _
        have reducedProductWeight :
            iteratedBivariateWeight tWeight
                (modulus * (C polynomial.leadingCoeff *
                  X ^ (polynomial.natDegree - modulus.natDegree))) ≤
              iteratedBivariateWeight tWeight polynomial := by
          calc
            iteratedBivariateWeight tWeight
                (modulus * (C polynomial.leadingCoeff *
                  X ^ (polynomial.natDegree - modulus.natDegree))) ≤
                iteratedBivariateWeight tWeight modulus +
                  iteratedBivariateWeight tWeight
                    (C polynomial.leadingCoeff *
                      X ^ (polynomial.natDegree - modulus.natDegree)) :=
              iteratedBivariateWeight_mul_le tWeight _ _
            _ ≤ modulus.natDegree * tWeight +
                (polynomial.leadingCoeff.natDegree +
                  (polynomial.natDegree - modulus.natDegree) * tWeight) :=
              Nat.add_le_add modulusWeight reductionMonomialWeight
            _ = polynomial.leadingCoeff.natDegree +
                polynomial.natDegree * tWeight := by
              calc
                modulus.natDegree * tWeight +
                    (polynomial.leadingCoeff.natDegree +
                      (polynomial.natDegree - modulus.natDegree) * tWeight) =
                    polynomial.leadingCoeff.natDegree +
                      (modulus.natDegree * tWeight +
                        (polynomial.natDegree - modulus.natDegree) *
                          tWeight) := by omega
                _ = polynomial.leadingCoeff.natDegree +
                    (modulus.natDegree +
                      (polynomial.natDegree - modulus.natDegree)) *
                        tWeight := by rw [Nat.add_mul]
                _ = polynomial.leadingCoeff.natDegree +
                    polynomial.natDegree * tWeight := by
                  rw [Nat.add_sub_of_le modulusDegreeLe]
            _ ≤ iteratedBivariateWeight tWeight polynomial := leadingLower
        have reducedWeight : iteratedBivariateWeight tWeight
            (polynomial - modulus * (C polynomial.leadingCoeff *
              X ^ (polynomial.natDegree - modulus.natDegree))) ≤
            iteratedBivariateWeight tWeight polynomial := by
          change iteratedBivariateWeight tWeight
            (polynomial + -(modulus * (C polynomial.leadingCoeff *
              X ^ (polynomial.natDegree - modulus.natDegree)))) ≤ _
          exact (iteratedBivariateWeight_add_le tWeight _ _).trans <|
            max_le le_rfl (by simpa using reducedProductWeight)
        unfold Polynomial.modByMonic Polynomial.divModByMonicAux
        dsimp
        rw [dif_pos modulusMonic, if_pos reducible]
        simpa only [Polynomial.modByMonic, dif_pos modulusMonic] using
          induction.trans reducedWeight
      else
        unfold Polynomial.modByMonic Polynomial.divModByMonicAux
        dsimp
        rw [dif_pos modulusMonic, if_neg reducible]
  termination_by polynomial => polynomial

#print axioms localBivariateWeight_add_le
#print axioms localBivariateWeight_mul_le
#print axioms weightedHomogeneousComponent_top_ne_zero
#print axioms weightedHomogeneousComponent_mul_top
#print axioms weightedTotalDegree_mul_eq
#print axioms localBivariateWeight_mul_eq
#print axioms localBivariateWeight_multiset_prod_eq
#print axioms localBivariateWeight_pow_le
#print axioms localBivariateWeight_C_le_natDegree
#print axioms localBivariateWeight_monomial_le
#print axioms localBivariateWeight_le_of_coeff
#print axioms iteratedBivariateWeight_add_le
#print axioms iteratedBivariateWeight_mul_le
#print axioms iteratedBivariateWeight_le_of_coeff
#print axioms iteratedBivariateWeight_modByMonic_le

end

end AspisK1.V7ExactCorrelatedAgreementRegularWeights
