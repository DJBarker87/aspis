import AspisFormal.K1.V7ExactCorrelatedAgreementRegularWeights
import AspisFormal.K1.V7ExactCorrelatedAgreementSmooth
import AspisFormal.K1.V7ExactCorrelatedAgreementHenselCombinatorics
import AspisFormal.V6PublishedTheoremInterfaces

/-!
# Exact additive factor budgets for V7 correlated agreement

The improved BCH+25 bound sums the individual weighted degrees of the
irreducible branches.  Charging every branch the parent's worst-case degree
introduces an extra factor of at most `112` and does not fit the released V7
challenge caps.  This file proves the required exact additivity over the
literal fixed prime-factor multisets.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementFactorBudgets

open Polynomial
open scoped Polynomial.Bivariate
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementLocalFactors
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Exact per-branch resultant budget used by the common-denominator
evaluation of a degree-`maximumDegree` candidate polynomial. -/
def fixedBranchEvaluationBudget
    (maximumDegree curveDegree globalDegree localDegree
      localWeight parentWeight : Nat) : Nat :=
  localDegree *
    ((localWeight + curveDegree - curveDegree * localDegree) +
      henselDenominatorExponent maximumDegree *
        ((parentWeight - curveDegree) + (globalDegree - 1) *
          (localWeight - curveDegree * localDegree)))

/-- A branch's literal budget is bounded by a product that is additive in
the local degree.  This coarse factor `4` is still comfortably inside both
unchanged V7 release caps. -/
theorem fixedBranchEvaluationBudget_le
    (maximumDegree curveDegree globalDegree localDegree
      localWeight parentWeight : Nat)
    (globalPositive : 0 < globalDegree)
    (curveLeLocal : curveDegree ≤ localWeight)
    (localLeParent : localWeight ≤ parentWeight) :
    fixedBranchEvaluationBudget maximumDegree curveDegree globalDegree
        localDegree localWeight parentWeight ≤
      4 * (maximumDegree + 1) * globalDegree * localDegree * parentWeight := by
  have exponentBound : henselDenominatorExponent maximumDegree ≤
      2 * maximumDegree := by
    unfold henselDenominatorExponent
    omega
  have generatorBound :
      localWeight + curveDegree - curveDegree * localDegree ≤
        2 * parentWeight := by
    calc
      localWeight + curveDegree - curveDegree * localDegree ≤
          localWeight + curveDegree := Nat.sub_le _ _
      _ ≤ parentWeight + parentWeight :=
        Nat.add_le_add localLeParent (curveLeLocal.trans localLeParent)
      _ = 2 * parentWeight := by ring
  have parentLeMul : parentWeight ≤ globalDegree * parentWeight := by
    calc
      parentWeight = 1 * parentWeight := by simp
      _ ≤ globalDegree * parentWeight :=
        Nat.mul_le_mul_right parentWeight (by omega)
  have etaBound :
      (parentWeight - curveDegree) + (globalDegree - 1) *
          (localWeight - curveDegree * localDegree) ≤
        2 * globalDegree * parentWeight := by
    calc
      (parentWeight - curveDegree) + (globalDegree - 1) *
          (localWeight - curveDegree * localDegree) ≤
          parentWeight + globalDegree * localWeight := by
        gcongr <;> omega
      _ ≤ globalDegree * parentWeight + globalDegree * parentWeight :=
        Nat.add_le_add parentLeMul (Nat.mul_le_mul_left _ localLeParent)
      _ = 2 * globalDegree * parentWeight := by ring
  unfold fixedBranchEvaluationBudget
  calc
    localDegree *
        ((localWeight + curveDegree - curveDegree * localDegree) +
          henselDenominatorExponent maximumDegree *
            ((parentWeight - curveDegree) + (globalDegree - 1) *
              (localWeight - curveDegree * localDegree))) ≤
      localDegree *
        (2 * parentWeight +
          (2 * maximumDegree) * (2 * globalDegree * parentWeight)) := by
        gcongr
    _ ≤ localDegree *
        (4 * (maximumDegree + 1) * globalDegree * parentWeight) := by
      gcongr
      have parentTerm : 2 * parentWeight ≤
          4 * globalDegree * parentWeight := by
        calc
          2 * parentWeight ≤ 2 * (globalDegree * parentWeight) :=
            Nat.mul_le_mul_left 2 parentLeMul
          _ ≤ 4 * (globalDegree * parentWeight) := by omega
          _ = 4 * globalDegree * parentWeight := by ring
      calc
        2 * parentWeight +
            2 * maximumDegree * (2 * globalDegree * parentWeight) ≤
          4 * globalDegree * parentWeight +
            2 * maximumDegree * (2 * globalDegree * parentWeight) :=
              Nat.add_le_add_right parentTerm _
        _ = 4 * (maximumDegree + 1) * globalDegree * parentWeight := by ring
    _ = 4 * (maximumDegree + 1) * globalDegree * localDegree * parentWeight := by
      ring

/-- The sharper form used by the exact V7 outer branch count.  Positivity of
the local `Y` degree makes the generator contribution no larger than the
literal local weight, removing the factor two lost by the completely generic
bound above. -/
theorem fixedBranchEvaluationBudget_le_two
    (maximumDegree curveDegree globalDegree localDegree
      localWeight parentWeight : Nat)
    (globalPositive : 0 < globalDegree)
    (localPositive : 0 < localDegree)
    (curveLeLocal : curveDegree ≤ localWeight)
    (localLeParent : localWeight ≤ parentWeight) :
    fixedBranchEvaluationBudget maximumDegree curveDegree globalDegree
        localDegree localWeight parentWeight ≤
      2 * (maximumDegree + 1) * globalDegree * localDegree * parentWeight := by
  have curveLeProduct : curveDegree ≤ curveDegree * localDegree := by
    calc
      curveDegree = curveDegree * 1 := by simp
      _ ≤ curveDegree * localDegree := Nat.mul_le_mul_left _ localPositive
  have generatorBound :
      localWeight + curveDegree - curveDegree * localDegree ≤ parentWeight := by
    rw [Nat.sub_le_iff_le_add]
    exact Nat.add_le_add localLeParent curveLeProduct
  have etaBound :
      (parentWeight - curveDegree) + (globalDegree - 1) *
          (localWeight - curveDegree * localDegree) ≤
        globalDegree * parentWeight := by
    calc
      (parentWeight - curveDegree) + (globalDegree - 1) *
          (localWeight - curveDegree * localDegree) ≤
        parentWeight + (globalDegree - 1) * parentWeight := by
          gcongr <;> omega
      _ = globalDegree * parentWeight := by
        calc
          parentWeight + (globalDegree - 1) * parentWeight =
              (1 + (globalDegree - 1)) * parentWeight := by ring
          _ = globalDegree * parentWeight := by
            congr 1
            omega
  have exponentBound : henselDenominatorExponent maximumDegree ≤
      2 * maximumDegree := by
    unfold henselDenominatorExponent
    omega
  unfold fixedBranchEvaluationBudget
  calc
    localDegree *
        ((localWeight + curveDegree - curveDegree * localDegree) +
          henselDenominatorExponent maximumDegree *
            ((parentWeight - curveDegree) + (globalDegree - 1) *
              (localWeight - curveDegree * localDegree))) ≤
      localDegree *
        (parentWeight + 2 * maximumDegree *
          (globalDegree * parentWeight)) := by
            gcongr
    _ ≤ localDegree *
        (2 * (maximumDegree + 1) * globalDegree * parentWeight) := by
      gcongr
      have parentLe : parentWeight ≤ globalDegree * parentWeight := by
        calc
          parentWeight = 1 * parentWeight := by simp
          _ ≤ globalDegree * parentWeight :=
            Nat.mul_le_mul_right parentWeight
              (Nat.succ_le_iff.mpr globalPositive)
      calc
        parentWeight + 2 * maximumDegree *
            (globalDegree * parentWeight) ≤
          globalDegree * parentWeight + 2 * maximumDegree *
            (globalDegree * parentWeight) := Nat.add_le_add_right parentLe _
        _ ≤ 2 * (maximumDegree + 1) * globalDegree * parentWeight := by
          calc
            globalDegree * parentWeight + 2 * maximumDegree *
                (globalDegree * parentWeight) ≤
              2 * (globalDegree * parentWeight) + 2 * maximumDegree *
                (globalDegree * parentWeight) := by omega
            _ = 2 * (maximumDegree + 1) * globalDegree * parentWeight := by
              ring
    _ = 2 * (maximumDegree + 1) * globalDegree * localDegree *
        parentWeight := by ring

/-- Coefficients under the concrete bivariate-to-multivariate equivalence.
Index `0` is the inner variable and index `1` is the outer variable. -/
theorem coeff_equivMvPolynomial
    {R : Type*} [CommRing R]
    (polynomial : BivariatePolynomial R) (inner outer : Nat) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) inner +
          Finsupp.single (1 : Fin 2) outer)
        (Polynomial.Bivariate.equivMvPolynomial R polynomial) =
      (polynomial.coeff outer).coeff inner := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add,
        leftInduction, rightInduction]
  | monomial outerExponent coefficient =>
      induction coefficient using Polynomial.induction_on' with
      | add left right leftInduction rightInduction =>
          simp only [map_add,
            MvPolynomial.coeff_add, Polynomial.coeff_add,
            leftInduction, rightInduction]
      | monomial innerExponent value =>
          have mapped : Polynomial.Bivariate.equivMvPolynomial R
              (Polynomial.monomial outerExponent
                (Polynomial.monomial innerExponent value)) =
              MvPolynomial.monomial
                (Finsupp.single (0 : Fin 2) innerExponent +
                  Finsupp.single (1 : Fin 2) outerExponent) value := by
            rw [← Polynomial.C_mul_X_pow_eq_monomial,
              ← Polynomial.C_mul_X_pow_eq_monomial]
            simp only [map_mul, map_pow,
              Polynomial.Bivariate.equivMvPolynomial_C_C,
              Polynomial.Bivariate.equivMvPolynomial_C_X,
              Polynomial.Bivariate.equivMvPolynomial_X]
            rw [MvPolynomial.C_mul_X_pow_eq_monomial,
              MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
            simp
          rw [mapped]
          simp only [MvPolynomial.coeff_monomial,
            Polynomial.coeff_monomial]
          have exponentEquality :
              (Finsupp.single (0 : Fin 2) innerExponent +
                    Finsupp.single (1 : Fin 2) outerExponent =
                  Finsupp.single (0 : Fin 2) inner +
                    Finsupp.single (1 : Fin 2) outer) ↔
                innerExponent = inner ∧ outerExponent = outer := by
            constructor
            · intro equality
              constructor
              · have coordinate := congrArg
                    (fun exponent : Fin 2 →₀ Nat => exponent (0 : Fin 2))
                    equality
                simpa using coordinate
              · have coordinate := congrArg
                    (fun exponent : Fin 2 →₀ Nat => exponent (1 : Fin 2))
                    equality
                simpa using coordinate
            · rintro ⟨rfl, rfl⟩
              rfl
          simp only [exponentEquality]
          by_cases innerEqual : innerExponent = inner <;>
            by_cases outerEqual : outerExponent = outer
          all_goals simp_all [Polynomial.coeff_monomial, eq_comm]

/-- Every nonzero outer coefficient contributes its literal
`inner-degree + outer-exponent * weight` to the multivariate definition. -/
theorem coeff_weight_le_localBivariateWeight
    {K : Type*} [CommRing K] [NoZeroDivisors K] [Nontrivial K]
    (tWeight : Nat)
    (polynomial : BivariatePolynomial K) (outer : Nat)
    (outerMem : outer ∈ polynomial.support) :
    (polynomial.coeff outer).natDegree + outer * tWeight ≤
      localBivariateWeight tWeight polynomial := by
  let inner := (polynomial.coeff outer).natDegree
  let monomial : Fin 2 →₀ Nat :=
    Finsupp.single (0 : Fin 2) inner + Finsupp.single (1 : Fin 2) outer
  have coefficientNeZero : polynomial.coeff outer ≠ 0 :=
    Polynomial.mem_support_iff.mp outerMem
  have mvCoefficientNeZero :
      MvPolynomial.coeff monomial
          (Polynomial.Bivariate.equivMvPolynomial K polynomial) ≠ 0 := by
    rw [show monomial = Finsupp.single (0 : Fin 2) inner +
        Finsupp.single (1 : Fin 2) outer by rfl,
      coeff_equivMvPolynomial]
    exact Polynomial.leadingCoeff_ne_zero.mpr coefficientNeZero
  have monomialMem : monomial ∈
      (Polynomial.Bivariate.equivMvPolynomial K polynomial).support :=
    MvPolynomial.mem_support_iff.mpr mvCoefficientNeZero
  have bounded := MvPolynomial.le_weightedTotalDegree
    (localWeightVector tWeight) monomialMem
  change Finsupp.weight (localWeightVector tWeight) monomial ≤
    localBivariateWeight tWeight polynomial at bounded
  simpa [monomial, inner, localWeightVector, map_add,
    Finsupp.weight_single] using bounded

/-- The multivariate and iterated-support presentations of the local weight
are literally equal over a field. -/
theorem localBivariateWeight_eq_iteratedBivariateWeight
    {K : Type*} [Field K] (tWeight : Nat)
    (polynomial : BivariatePolynomial K) :
    localBivariateWeight tWeight polynomial =
      iteratedBivariateWeight tWeight polynomial := by
  apply le_antisymm
  · apply localBivariateWeight_le_of_coeff
    intro exponent exponentMem
    exact coeff_weight_le_iteratedBivariateWeight tWeight polynomial exponent
      exponentMem
  · unfold iteratedBivariateWeight
    apply Finset.sup_le
    intro exponent exponentMem
    exact coeff_weight_le_localBivariateWeight tWeight polynomial exponent
      exponentMem

/-- Specializing the ignored innermost `X` variable cannot increase the
literal `(curveDegree,1)` weight in `(Y,Z)`. -/
theorem localBivariateWeight_specializeEvaluationPoint_le
    {K : Type*} [Field K] (curveDegree : Nat)
    (polynomial : TrivariatePolynomial K) (x : K) :
    localBivariateWeight curveDegree (specializeEvaluationPoint x polynomial) ≤
      localBivariateWeight curveDegree polynomial := by
  apply localBivariateWeight_le_of_coeff
  intro exponent exponentMem
  have specializedCoefficientNeZero :
      (specializeEvaluationPoint x polynomial).coeff exponent ≠ 0 :=
    Polynomial.mem_support_iff.mp exponentMem
  have originalCoefficientNeZero : polynomial.coeff exponent ≠ 0 := by
    intro originalZero
    apply specializedCoefficientNeZero
    simp [specializeEvaluationPoint, originalZero]
  have originalMem : exponent ∈ polynomial.support :=
    Polynomial.mem_support_iff.mpr originalCoefficientNeZero
  calc
    ((specializeEvaluationPoint x polynomial).coeff exponent).natDegree +
        exponent * curveDegree ≤
      (polynomial.coeff exponent).natDegree + exponent * curveDegree := by
        gcongr
        simpa [specializeEvaluationPoint, evaluateInnerVariable] using
          (Polynomial.natDegree_map_le
            (p := polynomial.coeff exponent)
            (f := Polynomial.evalRingHom x))
    _ ≤ localBivariateWeight curveDegree polynomial :=
      coeff_weight_le_localBivariateWeight curveDegree polynomial exponent
        originalMem

/-- Reorder `K[X,Z,Y]` to the bivariate polynomial in `(X,Y)` with
coefficient ring `K[Z]`, putting `Y` outermost. -/
noncomputable def trivariateXYPolynomial
    (K : Type*) [Field K] (polynomial : TrivariatePolynomial K) :
    BivariatePolynomial (Polynomial K) :=
  Polynomial.Bivariate.swap (trivariateXOuterEquiv K polynomial)

/-- `(1,k,0)`-weighted degree: `X` has weight one, `Y` has weight `k`, and
the challenge variable `Z` lives in the coefficient ring and has weight
zero. -/
def trivariateXYWeight
    {K : Type*} [Field K] (k : Nat)
    (polynomial : TrivariatePolynomial K) : Nat :=
  localBivariateWeight k (trivariateXYPolynomial K polynomial)

/-- `(0,curveDegree,1)`-weighted degree: `Y` has the scalar-curve degree,
`Z` has weight one, and the evaluation variable `X` is in the coefficient
ring with weight zero. -/
def trivariateYZWeight
    {K : Type*} [Field K] (curveDegree : Nat)
    (polynomial : TrivariatePolynomial K) : Nat :=
  localBivariateWeight curveDegree polynomial

theorem trivariateXYPolynomial_monomial
    {K : Type*} [Field K]
    (yExponent zExponent xExponent : Nat) (value : K) :
    trivariateXYPolynomial K
        (Polynomial.monomial yExponent
          (Polynomial.monomial zExponent
            (Polynomial.monomial xExponent value))) =
      Polynomial.monomial yExponent
        (Polynomial.monomial xExponent
          (Polynomial.monomial zExponent value)) := by
  rw [trivariateXYPolynomial, trivariateXOuterEquiv_monomial,
    Polynomial.Bivariate.swap_monomial_monomial]

theorem trivariateXYPolynomial_mul
    {K : Type*} [Field K]
    (left right : TrivariatePolynomial K) :
    trivariateXYPolynomial K (left * right) =
      trivariateXYPolynomial K left * trivariateXYPolynomial K right := by
  simp [trivariateXYPolynomial]

theorem trivariateXYPolynomial_injective
    {K : Type*} [Field K] :
    Function.Injective (trivariateXYPolynomial K) := by
  exact (Polynomial.Bivariate.swap (R := Polynomial K)).injective.comp
    (trivariateXOuterEquiv K).injective

/-- Every represented curve-interpolant monomial obeys its literal
`X + kY < xBound` constraint after reordering. -/
theorem trivariateXYWeight_curveTrivariatePolynomial_lt
    {K : Type*} [Field K]
    {maximumDegree curveDegree xBound yRows zBound : Nat}
    (xBoundPositive : 0 < xBound)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) :
    trivariateXYWeight maximumDegree
        (curveTrivariatePolynomial coefficients) < xBound := by
  classical
  apply lt_of_le_of_lt (b := xBound - 1)
  · unfold trivariateXYWeight trivariateXYPolynomial
    rw [curveTrivariatePolynomial, map_sum, map_sum]
    apply localBivariateWeight_finset_sum_le maximumDegree (xBound - 1)
    intro monomial _
    rw [trivariateXOuterEquiv_monomial,
      Polynomial.Bivariate.swap_monomial_monomial]
    exact (localBivariateWeight_monomial_le maximumDegree monomial.1.1
      (Polynomial.monomial monomial.2.1.1
        (Polynomial.monomial monomial.2.2 (coefficients monomial)))).trans <| by
          have weighted := monomial.2.1.2
          have subPositive :
              0 < xBound - maximumDegree * monomial.1.1 :=
            lt_of_le_of_lt (Nat.zero_le _) weighted
          have yWeightLt : maximumDegree * monomial.1.1 < xBound :=
            Nat.lt_of_sub_pos subPositive
          have yWeightLe : maximumDegree * monomial.1.1 ≤ xBound :=
            Nat.le_of_lt yWeightLt
          have subtractionIdentity :
              xBound - maximumDegree * monomial.1.1 +
                maximumDegree * monomial.1.1 = xBound :=
            Nat.sub_add_cancel yWeightLe
          have weightedSum : monomial.2.1.1 +
              maximumDegree * monomial.1.1 < xBound := by
            omega
          simp only [Polynomial.natDegree_monomial]
          by_cases coefficientZero : coefficients monomial = 0
          · simp [coefficientZero]
            have commute : monomial.1.1 * maximumDegree =
                maximumDegree * monomial.1.1 := Nat.mul_comm _ _
            omega
          · simp [coefficientZero]
            have commute : monomial.1.1 * maximumDegree =
                maximumDegree * monomial.1.1 := Nat.mul_comm _ _
            omega
  · omega

/-- The finite interpolant representation also gives its literal strict
`curveDegree * Y + Z < zBound` bound. -/
theorem trivariateYZWeight_curveTrivariatePolynomial_lt
    {K : Type*} [Field K]
    {maximumDegree curveDegree xBound yRows zBound : Nat}
    (zBoundPositive : 0 < zBound)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) :
    trivariateYZWeight curveDegree
        (curveTrivariatePolynomial coefficients) < zBound := by
  classical
  apply lt_of_le_of_lt (b := zBound - 1)
  · unfold trivariateYZWeight curveTrivariatePolynomial
    apply localBivariateWeight_finset_sum_le curveDegree (zBound - 1)
    intro monomial _
    exact (localBivariateWeight_monomial_le curveDegree monomial.1.1
      (Polynomial.monomial monomial.2.2.1
        (Polynomial.monomial monomial.2.1.1
          (coefficients monomial)))).trans <| by
          have weighted := monomial.2.2.2
          have subPositive :
              0 < zBound - curveDegree * monomial.1.1 :=
            lt_of_le_of_lt (Nat.zero_le _) weighted
          have yWeightLt : curveDegree * monomial.1.1 < zBound :=
            Nat.lt_of_sub_pos subPositive
          have yWeightLe : curveDegree * monomial.1.1 ≤ zBound :=
            Nat.le_of_lt yWeightLt
          have subtractionIdentity :
              zBound - curveDegree * monomial.1.1 +
                curveDegree * monomial.1.1 = zBound :=
            Nat.sub_add_cancel yWeightLe
          have weightedSum : monomial.2.2.1 +
              curveDegree * monomial.1.1 < zBound := by
            omega
          simp only [Polynomial.natDegree_monomial]
          by_cases coefficientZero : coefficients monomial = 0
          · simp [coefficientZero]
            have commute : monomial.1.1 * curveDegree =
                curveDegree * monomial.1.1 := Nat.mul_comm _ _
            omega
          · have innerMonomialNeZero :
                Polynomial.monomial monomial.2.1.1
                    (coefficients monomial) ≠ 0 := by
              simpa [Polynomial.monomial_eq_zero_iff] using coefficientZero
            simp [innerMonomialNeZero]
            have commute : monomial.1.1 * curveDegree =
                curveDegree * monomial.1.1 := Nat.mul_comm _ _
            omega
  · omega

/-- Additive `(0,curveDegree,1)` budget for the literal global factors. -/
theorem sum_positiveGlobalFactorYZWeights_le
    {K : Type*} [Field K] (curveDegree : Nat)
    (parent : TrivariatePolynomial K) (parentNeZero : parent ≠ 0) :
    ((positiveYPrimeFactors parent).map
      (trivariateYZWeight curveDegree)).sum ≤
        trivariateYZWeight curveDegree parent := by
  classical
  let factors := curvePrimeFactors parent
  have factorsPrime : ∀ factor ∈ factors, Prime factor :=
    curvePrimeFactors_prime parent parentNeZero
  have zeroNotMem : (0 : TrivariatePolynomial K) ∉ factors := by
    intro zeroMem
    exact (factorsPrime 0 zeroMem).ne_zero rfl
  have associatedProduct := curvePrimeFactors_product_associated parent
    parentNeZero
  have productNeZero : factors.prod ≠ (0 : TrivariatePolynomial K) := by
    intro productZero
    exact parentNeZero (associatedProduct.eq_zero_iff.mp productZero)
  obtain ⟨quotient, quotientEquation⟩ := associatedProduct.dvd
  have quotientNeZero : quotient ≠ 0 := by
    intro quotientZero
    rw [quotientZero, mul_zero] at quotientEquation
    exact parentNeZero quotientEquation
  have allFactorWeights :
      (factors.map (trivariateYZWeight curveDegree)).sum ≤
        trivariateYZWeight curveDegree parent := by
    rw [show (factors.map (trivariateYZWeight curveDegree)).sum =
        (factors.map (localBivariateWeight curveDegree)).sum by rfl]
    rw [← localBivariateWeight_multiset_prod_eq curveDegree factors
      zeroNotMem]
    calc
      localBivariateWeight curveDegree factors.prod ≤
          localBivariateWeight curveDegree factors.prod +
            localBivariateWeight curveDegree quotient := Nat.le_add_right _ _
      _ = trivariateYZWeight curveDegree parent := by
        rw [← localBivariateWeight_mul_eq curveDegree factors.prod quotient
          productNeZero quotientNeZero, quotientEquation]
        rfl
  have filteredWeightsLe :
      ((factors.filter fun factor ↦ 0 < factor.natDegree).map
          (trivariateYZWeight curveDegree)).sum ≤
        (factors.map (trivariateYZWeight curveDegree)).sum := by
    induction factors using Multiset.induction_on with
    | empty => simp
    | @cons factor factors induction =>
        by_cases positive : 0 < factor.natDegree
        · simp [positive, induction]
        · simp [positive]
          exact induction.trans (Nat.le_add_left _ _)
  exact filteredWeightsLe.trans allFactorWeights

/-- The sum of the actual positive-`Y` global branch weights is bounded by
the parent's `(1,k,0)` weight. -/
theorem sum_positiveGlobalFactorWeights_le
    {K : Type*} [Field K] (k : Nat)
    (parent : TrivariatePolynomial K) (parentNeZero : parent ≠ 0) :
    ((positiveYPrimeFactors parent).map (trivariateXYWeight k)).sum ≤
      trivariateXYWeight k parent := by
  classical
  let factors := curvePrimeFactors parent
  have factorsPrime : ∀ factor ∈ factors, Prime factor :=
    curvePrimeFactors_prime parent parentNeZero
  have zeroNotMem : (0 : TrivariatePolynomial K) ∉ factors := by
    intro zeroMem
    exact (factorsPrime 0 zeroMem).ne_zero rfl
  have mappedZeroNotMem :
      (0 : BivariatePolynomial (Polynomial K)) ∉
        factors.map (trivariateXYPolynomial K) := by
    rw [Multiset.mem_map]
    rintro ⟨factor, factorMem, factorMappedZero⟩
    have factorZero : factor = 0 := by
      apply trivariateXYPolynomial_injective
      simpa [trivariateXYPolynomial] using factorMappedZero
    exact zeroNotMem (factorZero ▸ factorMem)
  have associatedProduct := curvePrimeFactors_product_associated parent
    parentNeZero
  have productNeZero : factors.prod ≠ (0 : TrivariatePolynomial K) := by
    intro productZero
    exact parentNeZero (associatedProduct.eq_zero_iff.mp productZero)
  obtain ⟨quotient, quotientEquation⟩ := associatedProduct.dvd
  have quotientNeZero : quotient ≠ 0 := by
    intro quotientZero
    rw [quotientZero, mul_zero] at quotientEquation
    exact parentNeZero quotientEquation
  have mappedProductNeZero :
      trivariateXYPolynomial K factors.prod ≠ 0 :=
    by simpa [trivariateXYPolynomial] using
      trivariateXYPolynomial_injective.ne productNeZero
  have mappedQuotientNeZero :
      trivariateXYPolynomial K quotient ≠ 0 :=
    by simpa [trivariateXYPolynomial] using
      trivariateXYPolynomial_injective.ne quotientNeZero
  have allFactorWeights :
      (factors.map (trivariateXYWeight k)).sum ≤
        trivariateXYWeight k parent := by
    have mappedProducts :
        (factors.map (trivariateXYPolynomial K)).prod =
          trivariateXYPolynomial K factors.prod := by
      induction factors using Multiset.induction_on with
      | empty => simp [trivariateXYPolynomial]
      | @cons factor factors induction =>
          simp only [Multiset.map_cons, Multiset.prod_cons]
          rw [induction, trivariateXYPolynomial_mul]
    calc
      (factors.map (trivariateXYWeight k)).sum =
          ((factors.map (trivariateXYPolynomial K)).map
            (localBivariateWeight k)).sum := by
        simp [trivariateXYWeight, Function.comp_def]
      _ = localBivariateWeight k
          (factors.map (trivariateXYPolynomial K)).prod := by
        rw [localBivariateWeight_multiset_prod_eq k _ mappedZeroNotMem]
      _ = localBivariateWeight k (trivariateXYPolynomial K factors.prod) := by
        rw [mappedProducts]
      _ ≤ localBivariateWeight k (trivariateXYPolynomial K factors.prod) +
          localBivariateWeight k (trivariateXYPolynomial K quotient) :=
        Nat.le_add_right _ _
      _ = trivariateXYWeight k parent := by
        rw [← localBivariateWeight_mul_eq k _ _ mappedProductNeZero
          mappedQuotientNeZero, ← trivariateXYPolynomial_mul,
          quotientEquation]
        rfl
  have filteredWeightsLe :
      ((factors.filter fun factor ↦ 0 < factor.natDegree).map
          (trivariateXYWeight k)).sum ≤
        (factors.map (trivariateXYWeight k)).sum := by
    induction factors using Multiset.induction_on with
    | empty => simp
    | @cons factor factors induction =>
        by_cases positive : 0 < factor.natDegree
        · simp [positive, induction]
        · simp [positive]
          exact induction.trans (Nat.le_add_left _ _)
  exact filteredWeightsLe.trans allFactorWeights

/-! ## Local factorization budgets -/

/-- The sum of the actual local factor weights is bounded by the weight of
their parent.  Multiplicity is retained and no uniform branch bound is used. -/
theorem sum_positiveLocalFactorWeights_le
    {K : Type*} [Field K] (tWeight : Nat)
    (parent : BivariatePolynomial K) (parentNeZero : parent ≠ 0) :
    ((positiveYBivariatePrimeFactors parent).map
      (localBivariateWeight tWeight)).sum ≤
        localBivariateWeight tWeight parent := by
  classical
  let factors := bivariatePrimeFactors parent
  have factorsPrime : ∀ factor ∈ factors, Prime factor :=
    bivariatePrimeFactors_prime parent parentNeZero
  have zeroNotMem : (0 : BivariatePolynomial K) ∉ factors := by
    intro zeroMem
    exact (factorsPrime 0 zeroMem).ne_zero rfl
  have productNeZero : factors.prod ≠ 0 := Multiset.prod_ne_zero zeroNotMem
  have associatedProduct :=
    bivariatePrimeFactors_product_associated parent parentNeZero
  obtain ⟨quotient, quotientEquation⟩ := associatedProduct.dvd
  have quotientNeZero : quotient ≠ 0 := by
    intro quotientZero
    rw [quotientZero, mul_zero] at quotientEquation
    exact parentNeZero quotientEquation
  have allFactorWeights :
      (factors.map (localBivariateWeight tWeight)).sum ≤
        localBivariateWeight tWeight parent := by
    rw [← localBivariateWeight_multiset_prod_eq tWeight factors zeroNotMem]
    calc
      localBivariateWeight tWeight factors.prod ≤
          localBivariateWeight tWeight factors.prod +
            localBivariateWeight tWeight quotient := Nat.le_add_right _ _
      _ = localBivariateWeight tWeight parent := by
        rw [← localBivariateWeight_mul_eq tWeight factors.prod quotient
          productNeZero quotientNeZero, quotientEquation]
  have filteredWeightsLe :
      ((factors.filter fun factor ↦ 0 < factor.natDegree).map
          (localBivariateWeight tWeight)).sum ≤
        (factors.map (localBivariateWeight tWeight)).sum := by
    induction factors using Multiset.induction_on with
    | empty => simp
    | @cons factor factors induction =>
        by_cases positive : 0 < factor.natDegree
        · simp [positive, induction]
        · simp [positive]
          exact induction.trans (Nat.le_add_left _ _)
  exact filteredWeightsLe.trans allFactorWeights

/-! ## Exact release-cap arithmetic -/

/-- The improved fixed-branch algebraic budget, including one full
`curveDegree * domainSize + 1` concurrency reserve per possible `Y` branch
and the strict challenge-degree exceptional set, fits the released initial
cap. -/
theorem exactInitial_improvedBranchBudget_lt_releaseCap :
    (initialCurveZBound - 1) +
        2 * initialCurveXBound * initialCurveYRows ^ 2 *
          (initialCurveZBound - 1) +
        (initialBatchCurveDegree * 1048576 + 1) * initialCurveYRows <
      initialBatchChallengeCap := by
  norm_num [initialCurveXBound, initialCurveYRows, initialCurveZBound,
    initialBatchCurveDegree, initialBatchChallengeCap]

/-- The analogous conservative integer-113 final budget fits the unchanged
released fold cap. -/
theorem exactFinal_improvedBranchBudget_lt_releaseCap :
    (finalCurveZBound - 1) +
        2 * finalCurveXBound * finalCurveYRows ^ 2 *
          (finalCurveZBound - 1) +
        (foldCurveDegree * 262144 + 1) * finalCurveYRows <
      foldChallengeCap := by
  norm_num [finalCurveXBound, finalCurveYRows, finalCurveZBound,
    foldCurveDegree, foldChallengeCap]

/-- The concrete initial proximity gap converts the convenient per-branch
selection budget `29 * B + 28*n+1` into the exact support-incidence
inequality required by the heavy-coordinate theorem. -/
theorem exactInitial_incidence_of_branchSelection
    (branchBudget selectedCard : Nat)
    (selectedLarge :
      29 * branchBudget + (28 * 1048576 + 1) < selectedCard) :
    1024 * selectedCard + 1048576 * branchBudget <
      selectedCard * (38229 + 1) := by
  omega

/-- The same integer-29 scaling works for the exact final V7 parameters. -/
theorem exactFinal_incidence_of_branchSelection
    (branchBudget selectedCard : Nat)
    (selectedLarge :
      29 * branchBudget + (3 * 262144 + 1) < selectedCard) :
    255 * selectedCard + 262144 * branchBudget <
      selectedCard * (9557 + 1) := by
  omega

theorem exactInitial_concurrency_of_branchSelection
    (branchBudget selectedCard : Nat)
    (selectedLarge :
      29 * branchBudget + (28 * 1048576 + 1) < selectedCard) :
    28 * 1048576 < selectedCard := by omega

theorem exactFinal_concurrency_of_branchSelection
    (branchBudget selectedCard : Nat)
    (selectedLarge :
      29 * branchBudget + (3 * 262144 + 1) < selectedCard) :
    3 * 262144 < selectedCard := by omega

#print axioms coeff_equivMvPolynomial
#print axioms fixedBranchEvaluationBudget_le
#print axioms coeff_weight_le_localBivariateWeight
#print axioms localBivariateWeight_eq_iteratedBivariateWeight
#print axioms localBivariateWeight_specializeEvaluationPoint_le
#print axioms trivariateXYWeight_curveTrivariatePolynomial_lt
#print axioms trivariateYZWeight_curveTrivariatePolynomial_lt
#print axioms sum_positiveGlobalFactorWeights_le
#print axioms sum_positiveGlobalFactorYZWeights_le
#print axioms sum_positiveLocalFactorWeights_le
#print axioms exactInitial_improvedBranchBudget_lt_releaseCap
#print axioms exactFinal_improvedBranchBudget_lt_releaseCap
#print axioms exactInitial_incidence_of_branchSelection
#print axioms exactFinal_incidence_of_branchSelection
#print axioms exactInitial_concurrency_of_branchSelection
#print axioms exactFinal_concurrency_of_branchSelection

end

end AspisK1.V7ExactCorrelatedAgreementFactorBudgets
