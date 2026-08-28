import AspisFormal.K1.V7ExactCorrelatedAgreementRegularWeights
import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-!
# The integral local branch used by the exact V7 lift

BCIKS Appendix A replaces a local factor `H(Y,Z)`, with leading coefficient
`W(Z)`, by

`H̃(T,Z) = W(Z)^(deg H - 1) * H(T / W(Z), Z)`.

Mathlib's `Polynomial.integralNormalization` is exactly this coefficientwise
construction.  This file uses that released definition, proves the scaled
branch root satisfies the monic polynomial, and constructs the literal map
from the resulting finite `K[Z]`-algebra into the fixed function field.  No
division by a possibly vanishing specialization of `W` occurs here.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementRegularRing

open Polynomial
open scoped BigOperators
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementRegularWeights

noncomputable section

/-- The BCIKS integral normalization of a fixed local factor. -/
def integralLocalFactor
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    BivariatePolynomial K :=
  factor.integralNormalization

/-- A nonzero local factor has a monic integral normalization. -/
theorem integralLocalFactor_monic
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) :
    (integralLocalFactor factor).Monic := by
  exact Polynomial.monic_integralNormalization factorNeZero

/-- Integral normalization preserves the exact outer (`Y`/`T`) degree. -/
@[simp] theorem integralLocalFactor_natDegree
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :
    (integralLocalFactor factor).natDegree = factor.natDegree := by
  exact Polynomial.natDegree_integralNormalization

/-- The finite integral `K[Z]`-algebra cut out by the monicized factor. -/
abbrev IntegralLocalBranch
    {K : Type*} [Field K] (factor : BivariatePolynomial K) :=
  AdjoinRoot (integralLocalFactor factor)

/-- Embed coefficient polynomials `K[Z]` into the fixed branch field. -/
def regularCoefficientMap
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] :
    Polynomial K →+* LocalBranchField factor :=
  (AdjoinRoot.of (localFactorOverRational factor)).comp
    (algebraMap (Polynomial K) (ChallengeRationalField K))

/-- The coefficient embedding into the fixed branch field is injective. -/
theorem regularCoefficientMap_injective
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] :
    Function.Injective (regularCoefficientMap factor) := by
  exact (AdjoinRoot.of (localFactorOverRational factor)).injective.comp
    (IsFractionRing.injective (Polynomial K) (ChallengeRationalField K))

/-- The integral generator `T = W Y` inside the fixed branch field. -/
def integralBranchGenerator
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] :
    LocalBranchField factor :=
  regularCoefficientMap factor factor.leadingCoeff *
    AdjoinRoot.root (localFactorOverRational factor)

/-- The adjoined rational branch root is a literal root of the mapped local
factor, before any monicization. -/
theorem localFactor_eval₂_branchRoot
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] :
    factor.eval₂ (regularCoefficientMap factor)
        (AdjoinRoot.root (localFactorOverRational factor)) = 0 := by
  unfold regularCoefficientMap
  rw [← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root (localFactorOverRational factor)

/-- The integral generator is a root of the monicized factor.  This is the
exact algebraic identity `H̃(WY,Z) = W^(d-1) H(Y,Z)`, applied in the branch
field.  Injectivity is stated explicitly, so a vanishing leading coefficient
cannot be hidden by the coefficient embedding. -/
theorem integralBranchGenerator_isRoot
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] :
    (integralLocalFactor factor).eval₂ (regularCoefficientMap factor)
        (integralBranchGenerator factor) = 0 := by
  exact Polynomial.integralNormalization_eval₂_eq_zero
    (f := regularCoefficientMap factor)
    (z := AdjoinRoot.root (localFactorOverRational factor))
    (localFactor_eval₂_branchRoot factor)
    (fun coefficient coefficientZero ↦ by
      apply regularCoefficientMap_injective factor
      simpa only [map_zero] using coefficientZero)

/-- A base-field root `Y=y` of `H(Y,z)` gives the monicized root
`T=W(z)y`.  This identity remains valid when `W(z)=0`; no division or
degree-preservation assumption is made at specialization. -/
theorem integralLocalFactor_root_of_localFactor_root
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorPositive : 0 < factor.natDegree) (z y : K)
    (root : factor.eval₂ (Polynomial.evalRingHom z) y = 0) :
    (integralLocalFactor factor).eval₂ (Polynomial.evalRingHom z)
        ((factor.leadingCoeff).eval z * y) = 0 := by
  calc
    (integralLocalFactor factor).eval₂ (Polynomial.evalRingHom z)
        ((factor.leadingCoeff).eval z * y) =
        (Polynomial.evalRingHom z factor.leadingCoeff) ^
            (factor.natDegree - 1) *
          factor.eval₂ (Polynomial.evalRingHom z) y := by
      simpa [integralLocalFactor] using
        (Polynomial.integralNormalization_eval₂_leadingCoeff_mul
          factorPositive (Polynomial.evalRingHom z) y)
    _ = 0 := by rw [root, mul_zero]

/-- The literal map from the integral branch algebra into its rational
function field, sending the quotient generator to `T = W Y`. -/
def integralBranchToFunctionField
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] :
    IntegralLocalBranch factor →+* LocalBranchField factor :=
  AdjoinRoot.lift (regularCoefficientMap factor)
    (integralBranchGenerator factor)
    (integralBranchGenerator_isRoot factor)

@[simp] theorem integralBranchToFunctionField_root
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))] :
    integralBranchToFunctionField factor
        (AdjoinRoot.root (integralLocalFactor factor)) =
      integralBranchGenerator factor := by
  exact AdjoinRoot.lift_root (integralBranchGenerator_isRoot factor)

@[simp] theorem integralBranchToFunctionField_of
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    [Fact (Irreducible (localFactorOverRational factor))]
    (coefficient : Polynomial K) :
    integralBranchToFunctionField factor
        (AdjoinRoot.of (integralLocalFactor factor) coefficient) =
      regularCoefficientMap factor coefficient := by
  exact AdjoinRoot.lift_of (integralBranchGenerator_isRoot factor)

/-! ## Canonical regular representatives and rational substitutions -/

/-- The unique representative of outer degree below `deg H` in `K[Z][T]`.
This is the literal canonical regular representative used by BCIKS. -/
def canonicalRegularRepresentative
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) :
    IntegralLocalBranch factor →ₗ[Polynomial K] BivariatePolynomial K :=
  AdjoinRoot.modByMonicHom (integralLocalFactor_monic factor factorNeZero)

/-- The algebraic weight of a regular branch element is the weight of its
canonical representative. -/
def integralBranchWeight
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    (element : IntegralLocalBranch factor) : Nat :=
  localBivariateWeight generatorWeight
    (canonicalRegularRepresentative factor factorNeZero element)

/-- Iterated-support presentation of the same regular-element weight.  This
is used for the literal monic-division invariant. -/
def integralBranchIteratedWeight
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    (element : IntegralLocalBranch factor) : Nat :=
  iteratedBivariateWeight generatorWeight
    (canonicalRegularRepresentative factor factorNeZero element)

/-- Canonical representatives really represent their quotient element. -/
theorem mk_canonicalRegularRepresentative
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0)
    (element : IntegralLocalBranch factor) :
    AdjoinRoot.mk (integralLocalFactor factor)
        (canonicalRegularRepresentative factor factorNeZero element) =
      element := by
  exact AdjoinRoot.mk_leftInverse
    (integralLocalFactor_monic factor factorNeZero) element

/-- Under the genuine positive-degree hypothesis, the canonical
representative has strict outer degree below the local factor. -/
theorem canonicalRegularRepresentative_natDegree_lt
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (factorPositive : 0 < factor.natDegree)
    (element : IntegralLocalBranch factor) :
    (canonicalRegularRepresentative factor factorNeZero element).natDegree <
      factor.natDegree := by
  induction element using AdjoinRoot.induction_on with
  | ih representative =>
      change (representative %ₘ integralLocalFactor factor).natDegree <
        factor.natDegree
      rw [← integralLocalFactor_natDegree factor]
      apply Polynomial.natDegree_modByMonic_lt representative
        (integralLocalFactor_monic factor factorNeZero)
      intro normalizedOne
      have degreeOne := congrArg Polynomial.natDegree normalizedOne
      simp only [integralLocalFactor_natDegree,
        Polynomial.natDegree_one] at degreeOne
      omega

/-- Canonical representation of a quotient product is literal monic
reduction of the product of canonical representatives. -/
theorem canonicalRegularRepresentative_mul
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0)
    (left right : IntegralLocalBranch factor) :
    canonicalRegularRepresentative factor factorNeZero (left * right) =
      (canonicalRegularRepresentative factor factorNeZero left *
        canonicalRegularRepresentative factor factorNeZero right) %ₘ
          integralLocalFactor factor := by
  induction left using AdjoinRoot.induction_on with
  | ih leftRepresentative =>
      induction right using AdjoinRoot.induction_on with
      | ih rightRepresentative =>
          change (leftRepresentative * rightRepresentative) %ₘ
              integralLocalFactor factor =
            (leftRepresentative %ₘ integralLocalFactor factor) *
              (rightRepresentative %ₘ integralLocalFactor factor) %ₘ
                integralLocalFactor factor
          exact Polynomial.mul_modByMonic leftRepresentative
            rightRepresentative (integralLocalFactor factor)

/-- A root pair `(z,t)` of the monicized branch defines a literal ring
specialization from regular functions to the base field. -/
def integralBranchSpecialization
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (z t : K)
    (rootPair : (integralLocalFactor factor).eval₂
      (Polynomial.evalRingHom z) t = 0) :
    IntegralLocalBranch factor →+* K :=
  AdjoinRoot.lift (Polynomial.evalRingHom z) t rootPair

@[simp] theorem integralBranchSpecialization_root
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (z t : K)
    (rootPair : (integralLocalFactor factor).eval₂
      (Polynomial.evalRingHom z) t = 0) :
    integralBranchSpecialization factor z t rootPair
        (AdjoinRoot.root (integralLocalFactor factor)) = t := by
  exact AdjoinRoot.lift_root rootPair

@[simp] theorem integralBranchSpecialization_of
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (z t : K)
    (rootPair : (integralLocalFactor factor).eval₂
      (Polynomial.evalRingHom z) t = 0)
    (coefficient : Polynomial K) :
    integralBranchSpecialization factor z t rootPair
        (AdjoinRoot.of (integralLocalFactor factor) coefficient) =
      coefficient.eval z := by
  exact AdjoinRoot.lift_of rootPair

/-- Rational substitution is evaluation of the canonical representative.
This formulation is what permits the later resultant zero count. -/
theorem integralBranchSpecialization_eq_eval_canonical
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (z t : K)
    (rootPair : (integralLocalFactor factor).eval₂
      (Polynomial.evalRingHom z) t = 0)
    (element : IntegralLocalBranch factor) :
    integralBranchSpecialization factor z t rootPair element =
      (canonicalRegularRepresentative factor factorNeZero element).eval₂
        (Polynomial.evalRingHom z) t := by
  conv_lhs =>
    rw [← mk_canonicalRegularRepresentative factor factorNeZero element]
  exact AdjoinRoot.lift_mk rootPair _

/-! ## Weight of the monicized branch equation -/

/-- The coefficientwise invariant behind the BCIKS monicization bound. -/
theorem integralLocalFactor_coefficientWeight_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound) :
    ∀ exponent ∈ (integralLocalFactor factor).support,
      ((integralLocalFactor factor).coeff exponent).natDegree +
          exponent * (totalBound + ell - ell * factor.natDegree) ≤
        factor.natDegree *
          (totalBound + ell - ell * factor.natDegree) := by
  let degree := factor.natDegree
  let coefficientBudget := totalBound - ell * degree
  have leadingMem : degree ∈ factor.support := by
    exact Polynomial.natDegree_mem_support_of_nonzero factorNeZero
  have leadingBound := coefficientBound degree leadingMem
  have degreeWeightLe : ell * degree ≤ totalBound := by omega
  have generatorWeight : totalBound + ell - ell * degree =
      coefficientBudget + ell := by
    dsimp [coefficientBudget]
    omega
  intro exponent exponentMem
  rw [generatorWeight]
  have originalMem : exponent ∈ factor.support :=
    Polynomial.support_integralNormalization_subset exponentMem
  have exponentLe : exponent ≤ degree :=
    Polynomial.le_natDegree_of_mem_supp exponent originalMem
  rcases exponentLe.eq_or_lt with exponentEq | exponentLt
  · subst exponent
    have leadingCoefficient :
        (integralLocalFactor factor).coeff degree = 1 := by
      exact Polynomial.integralNormalization_coeff_natDegree factorNeZero
    rw [leadingCoefficient]
    simp [degree]
  · have exponentNe : exponent ≠ degree := Nat.ne_of_lt exponentLt
    have normalizedCoefficient :
        (integralLocalFactor factor).coeff exponent =
          factor.coeff exponent *
            factor.leadingCoeff ^ (degree - 1 - exponent) := by
      exact Polynomial.integralNormalization_coeff_ne_natDegree exponentNe
    rw [normalizedCoefficient]
    have originalBound := coefficientBound exponent originalMem
    have leadingDegree : factor.leadingCoeff.natDegree =
        (factor.coeff degree).natDegree := by
      rfl
    have leadingBudget : factor.leadingCoeff.natDegree ≤
        coefficientBudget := by
      rw [leadingDegree]
      dsimp [coefficientBudget]
      omega
    have coefficientDegree : (factor.coeff exponent).natDegree ≤
        coefficientBudget + ell * (degree - exponent) := by
      have totalDecomposition : totalBound =
          coefficientBudget + ell * degree := by
        dsimp [coefficientBudget]
        omega
      have degreeDecomposition : degree =
          exponent + (degree - exponent) := by omega
      have totalDecomposition' : totalBound =
          coefficientBudget + ell * exponent +
            ell * (degree - exponent) := by
        calc
          totalBound = coefficientBudget + ell * degree :=
            totalDecomposition
          _ = coefficientBudget +
              ell * (exponent + (degree - exponent)) := by
            exact congrArg (fun value => coefficientBudget + ell * value)
              degreeDecomposition
          _ = coefficientBudget + ell * exponent +
              ell * (degree - exponent) := by
            rw [Nat.mul_add, Nat.add_assoc]
      omega
    have normalizedDegree :
        (factor.coeff exponent *
          factor.leadingCoeff ^ (degree - 1 - exponent)).natDegree ≤
        (factor.coeff exponent).natDegree +
          (degree - 1 - exponent) * factor.leadingCoeff.natDegree :=
      Polynomial.natDegree_mul_le.trans <|
        Nat.add_le_add_left Polynomial.natDegree_pow_le _
    calc
      (factor.coeff exponent *
            factor.leadingCoeff ^ (degree - 1 - exponent)).natDegree +
          exponent * (coefficientBudget + ell) ≤
          ((factor.coeff exponent).natDegree +
            (degree - 1 - exponent) *
              factor.leadingCoeff.natDegree) +
            exponent * (coefficientBudget + ell) :=
        Nat.add_le_add_right normalizedDegree _
      _ ≤ (coefficientBudget + ell * (degree - exponent) +
            (degree - 1 - exponent) * coefficientBudget) +
          exponent * (coefficientBudget + ell) := by
        gcongr
      _ = degree * (coefficientBudget + ell) := by
        have decomposition : degree = exponent + 1 +
            (degree - 1 - exponent) := by omega
        have subtractDecomposition : degree - exponent =
            1 + (degree - 1 - exponent) := by omega
        rw [subtractDecomposition]
        conv_rhs => rw [decomposition]
        ring

/-- If `H` obeys the source weighted-degree bound
`deg_Z H_j + ell*j ≤ D`, then its integral normalization has weight at
most `d_H * (D + ell - ell*d_H)`. -/
theorem integralLocalFactor_weight_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound) :
    localBivariateWeight
        (totalBound + ell - ell * factor.natDegree)
        (integralLocalFactor factor) ≤
      factor.natDegree *
        (totalBound + ell - ell * factor.natDegree) := by
  apply localBivariateWeight_le_of_coeff
  exact integralLocalFactor_coefficientWeight_le factor factorNeZero ell
    totalBound coefficientBound

/-- The same monicization bound in the iterated-support presentation used
by the literal division proof. -/
theorem integralLocalFactor_iteratedWeight_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound) :
    iteratedBivariateWeight
        (totalBound + ell - ell * factor.natDegree)
        (integralLocalFactor factor) ≤
      factor.natDegree *
        (totalBound + ell - ell * factor.natDegree) := by
  apply iteratedBivariateWeight_le_of_coeff
  exact integralLocalFactor_coefficientWeight_le factor factorNeZero ell
    totalBound coefficientBound

/-! ## Weight laws in the regular quotient -/

/-- Multiplication in the actual regular quotient is subadditive for BCIKS
weight.  The modulus hypothesis is discharged from the coefficientwise
weighted-degree bound, then the literal canonical reduction theorem is used.
-/
theorem integralBranchIteratedWeight_mul_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (left right : IntegralLocalBranch factor) :
    integralBranchIteratedWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree) (left * right) ≤
      integralBranchIteratedWeight factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) left +
        integralBranchIteratedWeight factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) right := by
  let generatorWeight := totalBound + ell - ell * factor.natDegree
  let leftRep := canonicalRegularRepresentative factor factorNeZero left
  let rightRep := canonicalRegularRepresentative factor factorNeZero right
  have modulusWeight : iteratedBivariateWeight generatorWeight
      (integralLocalFactor factor) ≤
      (integralLocalFactor factor).natDegree * generatorWeight := by
    rw [integralLocalFactor_natDegree]
    exact integralLocalFactor_iteratedWeight_le factor factorNeZero ell
      totalBound coefficientBound
  change iteratedBivariateWeight generatorWeight
      (canonicalRegularRepresentative factor factorNeZero (left * right)) ≤
    iteratedBivariateWeight generatorWeight leftRep +
      iteratedBivariateWeight generatorWeight rightRep
  rw [canonicalRegularRepresentative_mul factor factorNeZero]
  exact (iteratedBivariateWeight_modByMonic_le generatorWeight
      (integralLocalFactor factor)
      (integralLocalFactor_monic factor factorNeZero) modulusWeight
      (leftRep * rightRep)).trans
    (iteratedBivariateWeight_mul_le generatorWeight leftRep rightRep)

/-- Addition in the regular quotient is submaximal for BCIKS weight. -/
theorem integralBranchIteratedWeight_add_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    (left right : IntegralLocalBranch factor) :
    integralBranchIteratedWeight factor factorNeZero generatorWeight
        (left + right) ≤
      max (integralBranchIteratedWeight factor factorNeZero generatorWeight left)
        (integralBranchIteratedWeight factor factorNeZero generatorWeight right) := by
  unfold integralBranchIteratedWeight canonicalRegularRepresentative
  rw [map_add]
  exact iteratedBivariateWeight_add_le generatorWeight _ _

@[simp] theorem integralBranchIteratedWeight_zero
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat) :
    integralBranchIteratedWeight factor factorNeZero generatorWeight 0 = 0 := by
  unfold integralBranchIteratedWeight canonicalRegularRepresentative
  rw [map_zero]
  exact iteratedBivariateWeight_zero generatorWeight

@[simp] theorem integralBranchIteratedWeight_one
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat) :
    integralBranchIteratedWeight factor factorNeZero generatorWeight 1 = 0 := by
  unfold integralBranchIteratedWeight canonicalRegularRepresentative
  change iteratedBivariateWeight generatorWeight
    (1 %ₘ integralLocalFactor factor) = 0
  by_cases degreeZero : (integralLocalFactor factor).natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero
      (integralLocalFactor_monic factor factorNeZero) degreeZero,
      Polynomial.modByMonic_one]
    exact iteratedBivariateWeight_zero generatorWeight
  · have degreePositive : 0 < (integralLocalFactor factor).natDegree :=
      Nat.pos_of_ne_zero degreeZero
    rw [(Polynomial.modByMonic_eq_self_iff
      (integralLocalFactor_monic factor factorNeZero)).mpr]
    · apply Nat.eq_zero_of_le_zero
      apply iteratedBivariateWeight_le_of_coeff generatorWeight 0 1
      intro exponent exponentMem
      have exponentZero : exponent = 0 := by
        by_contra exponentNeZero
        exact (Polynomial.mem_support_iff.mp exponentMem)
          (by simp [Polynomial.coeff_one, exponentNeZero])
      subst exponent
      simp
    · rw [Polynomial.degree_one,
        Polynomial.degree_eq_natDegree
          (integralLocalFactor_monic factor factorNeZero).ne_zero]
      exact_mod_cast degreePositive

@[simp] theorem integralBranchIteratedWeight_neg
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (generatorWeight : Nat)
    (element : IntegralLocalBranch factor) :
    integralBranchIteratedWeight factor factorNeZero generatorWeight
        (-element) =
      integralBranchIteratedWeight factor factorNeZero generatorWeight
        element := by
  unfold integralBranchIteratedWeight canonicalRegularRepresentative
  rw [map_neg]
  exact iteratedBivariateWeight_neg generatorWeight _

/-- Powers in the actual regular quotient cost at most the corresponding
multiple of the element's weight.  This is the form needed for the literal
`W` and `xi` powers in the denominator-cleared Hensel recurrence. -/
theorem integralBranchIteratedWeight_pow_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (element : IntegralLocalBranch factor) (power : Nat) :
    integralBranchIteratedWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree) (element ^ power) ≤
      power * integralBranchIteratedWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree) element := by
  induction power with
  | zero => simp
  | succ power induction =>
      rw [pow_succ, Nat.succ_mul]
      exact (integralBranchIteratedWeight_mul_le factor factorNeZero ell
        totalBound coefficientBound _ _).trans (Nat.add_le_add induction le_rfl)

/-- A finite sum of regular elements whose individual weights share one
ceiling has the same ceiling.  Cancellation can only lower the weight. -/
theorem integralBranchIteratedWeight_finset_sum_le
    {K ι : Type*} [Field K] [DecidableEq ι]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (generatorWeight bound : Nat) (indices : Finset ι)
    (element : ι → IntegralLocalBranch factor)
    (elementBound : ∀ index ∈ indices,
      integralBranchIteratedWeight factor factorNeZero generatorWeight
        (element index) ≤ bound) :
    integralBranchIteratedWeight factor factorNeZero generatorWeight
        (∑ index ∈ indices, element index) ≤ bound := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices indexNotMem induction =>
      rw [Finset.sum_insert indexNotMem]
      exact (integralBranchIteratedWeight_add_le factor factorNeZero
        generatorWeight _ _).trans <| max_le
          (elementBound index (Finset.mem_insert_self index indices))
          (induction (fun other otherMem => elementBound other
            (Finset.mem_insert_of_mem otherMem)))

/-- Weight of a finite product of actual regular-branch elements is bounded
by the sum of their individual weights. -/
theorem integralBranchIteratedWeight_finset_prod_le
    {K ι : Type*} [Field K]
    (factor : BivariatePolynomial K) (factorNeZero : factor ≠ 0)
    (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (indices : Finset ι) (element : ι → IntegralLocalBranch factor) :
    integralBranchIteratedWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree)
        (∏ index ∈ indices, element index) ≤
      ∑ index ∈ indices,
        integralBranchIteratedWeight factor factorNeZero
          (totalBound + ell - ell * factor.natDegree) (element index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices indexNotMem induction =>
      rw [Finset.prod_insert indexNotMem, Finset.sum_insert indexNotMem]
      exact (integralBranchIteratedWeight_mul_le factor factorNeZero ell
        totalBound coefficientBound _ _).trans (Nat.add_le_add le_rfl induction)

/-- Passing a literal polynomial representative into the integral quotient
does not increase weight.  This is the reusable entry point for the
denominator-cleared Hensel numerators. -/
theorem integralBranchIteratedWeight_mk_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (representative : BivariatePolynomial K) :
    integralBranchIteratedWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree)
        (AdjoinRoot.mk (integralLocalFactor factor) representative) ≤
      iteratedBivariateWeight
        (totalBound + ell - ell * factor.natDegree) representative := by
  let generatorWeight := totalBound + ell - ell * factor.natDegree
  have modulusWeight : iteratedBivariateWeight generatorWeight
      (integralLocalFactor factor) ≤
      (integralLocalFactor factor).natDegree * generatorWeight := by
    rw [integralLocalFactor_natDegree]
    exact integralLocalFactor_iteratedWeight_le factor factorNeZero ell
      totalBound coefficientBound
  change iteratedBivariateWeight generatorWeight
      (representative %ₘ integralLocalFactor factor) ≤
    iteratedBivariateWeight generatorWeight representative
  exact iteratedBivariateWeight_modByMonic_le generatorWeight
    (integralLocalFactor factor)
    (integralLocalFactor_monic factor factorNeZero) modulusWeight
    representative

/-- A coefficient polynomial embedded in the regular branch has no more
weight than its literal `Z` degree. -/
theorem integralBranchIteratedWeight_of_le_natDegree
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound)
    (coefficient : Polynomial K) :
    integralBranchIteratedWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree)
        (AdjoinRoot.of (integralLocalFactor factor) coefficient) ≤
      coefficient.natDegree := by
  unfold AdjoinRoot.of
  have reduced := integralBranchIteratedWeight_mk_le factor factorNeZero ell
    totalBound coefficientBound (C coefficient)
  exact reduced.trans <| by
    rw [← Polynomial.monomial_zero_left]
    simpa using iteratedBivariateWeight_monomial_le
      (totalBound + ell - ell * factor.natDegree) 0 coefficient

/-- The integral generator `T` has at most its declared generator weight in
the actual quotient. -/
theorem integralBranchIteratedWeight_root_le
    {K : Type*} [Field K] (factor : BivariatePolynomial K)
    (factorNeZero : factor ≠ 0) (ell totalBound : Nat)
    (coefficientBound : ∀ exponent ∈ factor.support,
      (factor.coeff exponent).natDegree + ell * exponent ≤ totalBound) :
    integralBranchIteratedWeight factor factorNeZero
        (totalBound + ell - ell * factor.natDegree)
        (AdjoinRoot.root (integralLocalFactor factor)) ≤
      totalBound + ell - ell * factor.natDegree := by
  have reduced := integralBranchIteratedWeight_mk_le factor factorNeZero ell
    totalBound coefficientBound X
  exact reduced.trans <| by
    rw [show (X : BivariatePolynomial K) =
      Polynomial.monomial 1 1 by rfl]
    simpa using iteratedBivariateWeight_monomial_le
      (totalBound + ell - ell * factor.natDegree) 1
        (1 : Polynomial K)

#print axioms integralLocalFactor_monic
#print axioms integralBranchGenerator_isRoot
#print axioms integralLocalFactor_root_of_localFactor_root
#print axioms integralBranchToFunctionField_root
#print axioms canonicalRegularRepresentative_natDegree_lt
#print axioms integralBranchSpecialization_eq_eval_canonical
#print axioms integralLocalFactor_coefficientWeight_le
#print axioms integralLocalFactor_weight_le
#print axioms integralLocalFactor_iteratedWeight_le
#print axioms canonicalRegularRepresentative_mul
#print axioms integralBranchIteratedWeight_mul_le
#print axioms integralBranchIteratedWeight_add_le
#print axioms integralBranchIteratedWeight_pow_le
#print axioms integralBranchIteratedWeight_finset_sum_le
#print axioms integralBranchIteratedWeight_finset_prod_le
#print axioms integralBranchIteratedWeight_mk_le
#print axioms integralBranchIteratedWeight_of_le_natDegree
#print axioms integralBranchIteratedWeight_root_le

end

end AspisK1.V7ExactCorrelatedAgreementRegularRing
