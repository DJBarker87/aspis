import AspisFormal.K1.V7Tag73ExactGRSConversion
import AspisFormal.V6OneFoldParameterAudit

/-!
# Exact multiplicity-three Guruswami--Sudan parameters for V7

This file develops only the interpolation and root machinery required by the
two exact GRS instances used by Tag 73.  In particular, the initial circle
message image is kept as its proved 1024-dimensional subcode of the ambient
degree-at-most-1024 GRS code.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactMultiplicityThreeGS

open scoped BigOperators
open Polynomial
open AspisK1.V7Tag73ExactGRSConversion
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldParameterAudit

/-! ## Exact degree convention -/

/-- The published initial `rate = 1/1024` calculation uses the ambient GRS
maximum degree `1024`, divided by the exact word length.  It is not the rate
obtained from a hypothetical strict degree bound `< 1024` (maximum degree
`1023`). -/
theorem exactInitialAmbientDegreeConvention :
    (∀ message : InitialMessage QM31Exact,
      (exactInitialGRSConversion.messagePolynomial message).natDegree ≤ 1024) ∧
      initialRate = (1024 : Real) / 1048576 ∧
      initialRate ≠ (1023 : Real) / 1048576 := by
  constructor
  · exact exactInitialGRSConversion.messagePolynomial_degree_le
  constructor <;> norm_num [initialRate]

/-- The final published rate likewise uses maximum degree `255`, not message
dimension `256`, divided by the exact line-domain length. -/
theorem exactFinalAmbientDegreeConvention :
    (∀ message : FinalMessage QM31Exact,
      (exactFinalGRSConversion.messagePolynomial message).natDegree ≤ 255) ∧
      outputRate = (255 : Real) / 262144 := by
  constructor
  · exact exactFinalGRSConversion.messagePolynomial_degree_le
  · rfl

/-! ## Exact interpolation budgets -/

def multiplicity : Nat := 3
def yDegree : Nat := 112
def finalWeightedDegree : Nat := 28673
def initialWeightedDegree : Nat := 114689

/-- Number of monomials `X^i Y^j` with `0 <= j <= ell` and
`i + d*j <= D`.  The exact instances below satisfy `d*ell <= D`, so every
summand is the intended nonempty row of the weighted-degree triangle. -/
def weightedMonomialCount (maximumDegree weightedDegree ell : Nat) : Nat :=
  (Finset.range (ell + 1)).sum
    (fun j => weightedDegree - maximumDegree * j + 1)

/-- At the final V7 parameters the multiplicity-three interpolation space has
1,626,522 coefficients, strictly more than the 1,572,864 homogeneous Hasse
constraints.  Its weighted degree is also strictly below `3 * 9558`, which is
the root-forcing inequality. -/
theorem exactFinalInterpolationBudget :
    weightedMonomialCount 255 finalWeightedDegree yDegree = 1626522 ∧
      6 * 262144 < weightedMonomialCount 255 finalWeightedDegree yDegree ∧
      finalWeightedDegree < multiplicity * 9558 ∧
      255 * yDegree ≤ finalWeightedDegree ∧
      finalWeightedDegree < 255 * (yDegree + 1) := by
  norm_num [weightedMonomialCount, finalWeightedDegree, yDegree, multiplicity,
    Finset.sum_range_succ]

/-- The initial ambient degree is exactly `1024`.  With that convention the
same `Y`-degree gives 6,480,098 coefficients, strictly more than the
6,291,456 interpolation constraints, while `D < 3 * 38230`. -/
theorem exactInitialInterpolationBudget :
    weightedMonomialCount 1024 initialWeightedDegree yDegree = 6480098 ∧
      6 * 1048576 < weightedMonomialCount 1024 initialWeightedDegree yDegree ∧
      initialWeightedDegree < multiplicity * 38230 ∧
      1024 * yDegree ≤ initialWeightedDegree ∧
      initialWeightedDegree < 1024 * (yDegree + 1) := by
  norm_num [weightedMonomialCount, initialWeightedDegree, yDegree, multiplicity,
    Finset.sum_range_succ]

/-! ## Multiplicity-three interpolation system -/

/-- Coefficients of the weighted-degree interpolation polynomial are indexed
row-by-row in `Y`: row `j` contains exactly the powers
`X^0, ..., X^(D-d*j)`. -/
abbrev WeightedMonomialIndex
    (maximumDegree weightedDegree ell : Nat) :=
  Σ j : Fin (ell + 1), Fin (weightedDegree - maximumDegree * j.1 + 1)

theorem weightedMonomialIndex_card
    (maximumDegree weightedDegree ell : Nat) :
    Fintype.card (WeightedMonomialIndex maximumDegree weightedDegree ell) =
      weightedMonomialCount maximumDegree weightedDegree ell := by
  simp only [WeightedMonomialIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [weightedMonomialCount, ← Fin.sum_univ_eq_sum_range]

/-- The six bivariate Hasse constraints of total derivative order below
three, ordered as `(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)`. -/
def hasseXOrder (constraint : Fin 6) : Nat :=
  match constraint.1 with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | _ => 0

def hasseYOrder (constraint : Fin 6) : Nat :=
  match constraint.1 with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 1
  | _ => 2

@[simp] theorem hasseXOrder_zero : hasseXOrder (0 : Fin 6) = 0 := rfl
@[simp] theorem hasseYOrder_zero : hasseYOrder (0 : Fin 6) = 0 := rfl
@[simp] theorem hasseXOrder_one : hasseXOrder (1 : Fin 6) = 1 := rfl
@[simp] theorem hasseYOrder_one : hasseYOrder (1 : Fin 6) = 0 := rfl
@[simp] theorem hasseXOrder_two : hasseXOrder (2 : Fin 6) = 0 := rfl
@[simp] theorem hasseYOrder_two : hasseYOrder (2 : Fin 6) = 1 := rfl
@[simp] theorem hasseXOrder_three : hasseXOrder (3 : Fin 6) = 2 := rfl
@[simp] theorem hasseYOrder_three : hasseYOrder (3 : Fin 6) = 0 := rfl
@[simp] theorem hasseXOrder_four : hasseXOrder (4 : Fin 6) = 1 := rfl
@[simp] theorem hasseYOrder_four : hasseYOrder (4 : Fin 6) = 1 := rfl
@[simp] theorem hasseXOrder_five : hasseXOrder (5 : Fin 6) = 0 := rfl
@[simp] theorem hasseYOrder_five : hasseYOrder (5 : Fin 6) = 2 := rfl

theorem hasseOrder_sum_lt_three (constraint : Fin 6) :
    hasseXOrder constraint + hasseYOrder constraint < 3 := by
  fin_cases constraint <;> decide

noncomputable section

private theorem qm31ExactTwoNeZero : (2 : QM31Exact) ≠ 0 := by
  intro equalZero
  have mapped :
      algebraMap M31Exact QM31Exact (2 : M31Exact) =
        algebraMap M31Exact QM31Exact 0 := by
    simpa only [map_ofNat, map_zero] using equalZero
  have baseEqual := FaithfulSMul.algebraMap_injective M31Exact QM31Exact mapped
  exact AspisCircleGroupOrder.two_ne_zero_ZModP baseEqual

local instance qm31ExactNeZeroTwo : NeZero (2 : QM31Exact) :=
  ⟨qm31ExactTwoNeZero⟩

/-- One homogeneous bivariate Hasse condition on the coefficient vector.
The point is `(x,y)` and `constraint` selects one derivative pair of total
order below three. -/
def interpolationConstraint
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (x y : K) (constraint : Fin 6) :
    (WeightedMonomialIndex maximumDegree weightedDegree ell → K) →ₗ[K] K where
  toFun coefficients :=
    ∑ monomial,
      coefficients monomial *
        (monomial.2.1.choose (hasseXOrder constraint) : K) *
        x ^ (monomial.2.1 - hasseXOrder constraint) *
        (monomial.1.1.choose (hasseYOrder constraint) : K) *
        y ^ (monomial.1.1 - hasseYOrder constraint)
  map_add' left right := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro monomial _
    simp only [RingHom.id_apply]
    ring

@[simp] theorem interpolationConstraint_apply
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (x y : K) (constraint : Fin 6)
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K) :
    interpolationConstraint x y constraint coefficients =
      ∑ monomial,
        coefficients monomial *
          (monomial.2.1.choose (hasseXOrder constraint) : K) *
          x ^ (monomial.2.1 - hasseXOrder constraint) *
          (monomial.1.1.choose (hasseYOrder constraint) : K) *
          y ^ (monomial.1.1 - hasseYOrder constraint) := rfl

/-- All six multiplicity-three constraints at every interpolation point. -/
def interpolationMap
    {K : Type*} [Field K]
    {n maximumDegree weightedDegree ell : Nat}
    (points values : Fin n → K) :
    (WeightedMonomialIndex maximumDegree weightedDegree ell → K) →ₗ[K]
      (Fin n → Fin 6 → K) where
  toFun coefficients index constraint :=
    interpolationConstraint (points index) (values index) constraint
      coefficients
  map_add' left right := by
    funext index constraint
    exact LinearMap.map_add _ _ _
  map_smul' scalar coefficients := by
    funext index constraint
    exact LinearMap.map_smul _ _ _

/-- Substitute a univariate candidate `f(X)` for `Y` in the interpolation
coefficient vector.  This is the ordinary polynomial `Q(X,f(X))`. -/
def interpolationSubstitute
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (candidate : K[X]) : K[X] :=
  ∑ monomial,
    C (coefficients monomial) * X ^ monomial.2.1 *
      candidate ^ monomial.1.1

theorem weightedMonomialIndex_degree
    {maximumDegree weightedDegree ell : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (monomial : WeightedMonomialIndex maximumDegree weightedDegree ell) :
    monomial.2.1 + maximumDegree * monomial.1.1 ≤ weightedDegree := by
  have row_le : monomial.1.1 ≤ ell := by
    exact Nat.le_of_lt_succ (by simpa using monomial.1.2)
  have row_weight_le : maximumDegree * monomial.1.1 ≤ weightedDegree :=
    (Nat.mul_le_mul_left maximumDegree row_le).trans lastRow
  have column_le :
      monomial.2.1 ≤ weightedDegree - maximumDegree * monomial.1.1 := by
    omega
  omega

/-- Weighted degree controls the ordinary degree after substituting any
candidate of degree at most `maximumDegree`. -/
theorem interpolationSubstitute_natDegree_le
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (candidate : K[X]) (candidateDegree : candidate.natDegree ≤ maximumDegree) :
    (interpolationSubstitute coefficients candidate).natDegree ≤
      weightedDegree := by
  classical
  unfold interpolationSubstitute
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro monomial _
  have coefficientDegree :
      (C (coefficients monomial)).natDegree ≤ 0 := by
    simp
  have xDegree : (X ^ monomial.2.1 : K[X]).natDegree ≤ monomial.2.1 := by
    simp
  have candidatePowerDegree :
      (candidate ^ monomial.1.1).natDegree ≤
        monomial.1.1 * maximumDegree := by
    exact Polynomial.natDegree_pow_le.trans
      (Nat.mul_le_mul_left monomial.1.1 candidateDegree)
  have firstProduct :
      (C (coefficients monomial) * X ^ monomial.2.1 : K[X]).natDegree ≤
        (C (coefficients monomial)).natDegree +
          (X ^ monomial.2.1 : K[X]).natDegree :=
    Polynomial.natDegree_mul_le
  have wholeProduct :
      (C (coefficients monomial) * X ^ monomial.2.1 *
          candidate ^ monomial.1.1).natDegree ≤
        (C (coefficients monomial) * X ^ monomial.2.1 : K[X]).natDegree +
          (candidate ^ monomial.1.1).natDegree :=
    Polynomial.natDegree_mul_le
  have weight := weightedMonomialIndex_degree lastRow monomial
  calc
    (C (coefficients monomial) * X ^ monomial.2.1 *
        candidate ^ monomial.1.1).natDegree
        ≤ (C (coefficients monomial) * X ^ monomial.2.1 : K[X]).natDegree +
            (candidate ^ monomial.1.1).natDegree := wholeProduct
    _ ≤ (0 + monomial.2.1) + monomial.1.1 * maximumDegree :=
      Nat.add_le_add
        (firstProduct.trans (Nat.add_le_add coefficientDegree xDegree))
        candidatePowerDegree
    _ = monomial.2.1 + maximumDegree * monomial.1.1 := by
      simp [Nat.mul_comm]
    _ ≤ weightedDegree := weight

/-- The order-zero interpolation constraint is evaluation of
`Q(X,f(X))` at a point where `f(x)=y`. -/
theorem interpolationSubstitute_eval
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (candidate : K[X]) (x : K) :
    (interpolationSubstitute coefficients candidate).eval x =
      interpolationConstraint x (candidate.eval x) (0 : Fin 6)
        coefficients := by
  classical
  simp [interpolationSubstitute, interpolationConstraint, hasseXOrder,
    hasseYOrder, Polynomial.eval_finsetSum]

/-- The first derivative of `Q(X,f(X))` is the expected chain-rule
combination of the `(1,0)` and `(0,1)` Hasse constraints. -/
theorem interpolationSubstitute_derivative_eval
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (candidate : K[X]) (x : K) :
    (interpolationSubstitute coefficients candidate).derivative.eval x =
      interpolationConstraint x (candidate.eval x) (1 : Fin 6)
          coefficients +
        candidate.derivative.eval x *
          interpolationConstraint x (candidate.eval x) (2 : Fin 6)
            coefficients := by
  classical
  rw [interpolationConstraint_apply, interpolationConstraint_apply,
    hasseXOrder_one, hasseYOrder_one, hasseXOrder_two, hasseYOrder_two]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    mul_one, Nat.sub_zero]
  unfold interpolationSubstitute
  change
    (derivative (∑ monomial,
      C (coefficients monomial) * X ^ monomial.2.1 *
        candidate ^ monomial.1.1)).eval x =
    (∑ monomial,
      coefficients monomial * (monomial.2.1 : K) *
        x ^ (monomial.2.1 - 1) * candidate.eval x ^ monomial.1.1) +
      candidate.derivative.eval x *
        ∑ monomial,
          coefficients monomial * x ^ monomial.2.1 *
            (monomial.1.1 : K) *
              candidate.eval x ^ (monomial.1.1 - 1)
  simp only [map_sum, Polynomial.eval_finsetSum,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
    Finset.sum_add_distrib, zero_mul, zero_add,
    Polynomial.derivative_X, Polynomial.eval_one]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro monomial _
  ring

private theorem two_mul_cast_choose_two
    {K : Type*} [Field K] (n : Nat) :
    (2 : K) * (n.choose 2 : K) =
      (n : K) * ((n - 1 : Nat) : K) := by
  have natural : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right, mul_comm]
    exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)
  simpa only [Nat.cast_ofNat, Nat.cast_mul] using
    congrArg (fun value : Nat => (value : K)) natural

private theorem second_derivative_monomial_eval
    {K : Type*} [Field K]
    (coefficient x : K) (xDegree yDegree : Nat) (candidate : K[X]) :
    (derivative (derivative
      (C coefficient * X ^ xDegree * candidate ^ yDegree))).eval x =
      coefficient * (xDegree : K) * ((xDegree - 1 : Nat) : K) *
        x ^ (xDegree - 2) * candidate.eval x ^ yDegree +
      2 * candidate.derivative.eval x *
        (coefficient * (xDegree : K) * x ^ (xDegree - 1) *
          (yDegree : K) * candidate.eval x ^ (yDegree - 1)) +
      (derivative (derivative candidate)).eval x *
        (coefficient * x ^ xDegree * (yDegree : K) *
          candidate.eval x ^ (yDegree - 1)) +
      candidate.derivative.eval x ^ 2 *
        (coefficient * x ^ xDegree * (yDegree : K) *
          ((yDegree - 1 : Nat) : K) *
            candidate.eval x ^ (yDegree - 2)) := by
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C,
    Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_one,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero,
    Polynomial.eval_one, zero_mul, zero_add, Nat.sub_sub,
    one_add_one_eq_two]
  ring

private theorem two_mul_interpolationConstraint_three
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (x y : K) :
    2 * interpolationConstraint x y (3 : Fin 6) coefficients =
      ∑ monomial,
        coefficients monomial * (monomial.2.1 : K) *
          ((monomial.2.1 - 1 : Nat) : K) *
            x ^ (monomial.2.1 - 2) * y ^ monomial.1.1 := by
  classical
  rw [interpolationConstraint_apply, hasseXOrder_three,
    hasseYOrder_three]
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro monomial _
  have identity := two_mul_cast_choose_two (K := K) monomial.2.1
  linear_combination
    (coefficients monomial * x ^ (monomial.2.1 - 2) *
      y ^ monomial.1.1) * identity

private theorem two_mul_interpolationConstraint_five
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (x y : K) :
    2 * interpolationConstraint x y (5 : Fin 6) coefficients =
      ∑ monomial,
        coefficients monomial * x ^ monomial.2.1 *
          (monomial.1.1 : K) * ((monomial.1.1 - 1 : Nat) : K) *
            y ^ (monomial.1.1 - 2) := by
  classical
  rw [interpolationConstraint_apply, hasseXOrder_five,
    hasseYOrder_five]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro monomial _
  have identity := two_mul_cast_choose_two (K := K) monomial.1.1
  linear_combination
    (coefficients monomial * x ^ monomial.2.1 *
      y ^ (monomial.1.1 - 2)) * identity

/-- The second derivative is the multiplicity-three chain rule.  Writing it
with Hasse constraints avoids division by `2` and is valid in every field. -/
theorem interpolationSubstitute_second_derivative_eval
    {K : Type*} [Field K]
    {maximumDegree weightedDegree ell : Nat}
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (candidate : K[X]) (x : K) :
    (derivative (derivative
      (interpolationSubstitute coefficients candidate))).eval x =
      2 * interpolationConstraint x (candidate.eval x) (3 : Fin 6)
          coefficients +
      2 * candidate.derivative.eval x *
        interpolationConstraint x (candidate.eval x) (4 : Fin 6)
          coefficients +
      (derivative (derivative candidate)).eval x *
        interpolationConstraint x (candidate.eval x) (2 : Fin 6)
          coefficients +
      2 * candidate.derivative.eval x ^ 2 *
        interpolationConstraint x (candidate.eval x) (5 : Fin 6)
          coefficients := by
  classical
  calc
    (derivative (derivative
        (interpolationSubstitute coefficients candidate))).eval x =
        ∑ monomial,
          (derivative (derivative
            (C (coefficients monomial) * X ^ monomial.2.1 *
              candidate ^ monomial.1.1))).eval x := by
      simp only [interpolationSubstitute, map_sum,
        Polynomial.eval_finsetSum]
    _ = ∑ monomial,
        (coefficients monomial * (monomial.2.1 : K) *
              ((monomial.2.1 - 1 : Nat) : K) *
              x ^ (monomial.2.1 - 2) *
              candidate.eval x ^ monomial.1.1 +
          2 * candidate.derivative.eval x *
            (coefficients monomial * (monomial.2.1 : K) *
              x ^ (monomial.2.1 - 1) * (monomial.1.1 : K) *
              candidate.eval x ^ (monomial.1.1 - 1)) +
          (derivative (derivative candidate)).eval x *
            (coefficients monomial * x ^ monomial.2.1 *
              (monomial.1.1 : K) *
              candidate.eval x ^ (monomial.1.1 - 1)) +
          candidate.derivative.eval x ^ 2 *
            (coefficients monomial * x ^ monomial.2.1 *
              (monomial.1.1 : K) *
              ((monomial.1.1 - 1 : Nat) : K) *
              candidate.eval x ^ (monomial.1.1 - 2))) := by
      apply Finset.sum_congr rfl
      intro monomial _
      exact second_derivative_monomial_eval
        (coefficients monomial) x monomial.2.1 monomial.1.1 candidate
    _ = _ := by
      rw [two_mul_interpolationConstraint_three]
      rw [show
        2 * candidate.derivative.eval x ^ 2 *
            interpolationConstraint x (candidate.eval x) (5 : Fin 6)
              coefficients =
          candidate.derivative.eval x ^ 2 *
            (2 * interpolationConstraint x (candidate.eval x) (5 : Fin 6)
              coefficients) by ring]
      rw [two_mul_interpolationConstraint_five]
      rw [interpolationConstraint_apply, interpolationConstraint_apply,
        hasseXOrder_four, hasseYOrder_four, hasseXOrder_two,
        hasseYOrder_two]
      simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
        mul_one, Nat.sub_zero]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      simp only [Finset.sum_add_distrib]

private theorem two_mul_taylor_coeff_two
    {K : Type*} [Field K] (polynomial : K[X]) (x : K) :
    2 * (Polynomial.taylor x polynomial).coeff 2 =
      (derivative (derivative polynomial)).eval x := by
  rw [Polynomial.taylor_coeff]
  have relation := congrFun
    (Polynomial.factorial_smul_hasseDeriv (R := K) 2) polynomial
  have evaluated := congrArg (fun p : K[X] => p.eval x) relation
  simpa [Function.iterate_succ_apply', nsmul_eq_mul] using evaluated

/-- A kernel vector satisfies every one of its six pointwise Hasse
constraints. -/
theorem interpolationConstraint_eq_zero_of_mem_kernel
    {K : Type*} [Field K]
    {n maximumDegree weightedDegree ell : Nat}
    (points values : Fin n → K)
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (kernel : interpolationMap points values coefficients = 0)
    (index : Fin n) (constraint : Fin 6) :
    interpolationConstraint (points index) (values index) constraint
      coefficients = 0 := by
  have pointwise := congrFun (congrFun kernel index) constraint
  simpa [interpolationMap] using pointwise

/-- At every coordinate where a candidate polynomial matches the
interpolation value, all six multiplicity-three constraints force
`(X-a)^3` to divide `Q(X,f(X))`. -/
theorem interpolationMultiplicityThree_dvd
    {K : Type*} [Field K] [NeZero (2 : K)]
    {n maximumDegree weightedDegree ell : Nat}
    (points values : Fin n → K)
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (kernel : interpolationMap points values coefficients = 0)
    (candidate : K[X]) (index : Fin n)
    (agreementAt : candidate.eval (points index) = values index) :
    (X - C (points index)) ^ 3 ∣
      interpolationSubstitute coefficients candidate := by
  let substituted := interpolationSubstitute coefficients candidate
  have constraintZero (constraint : Fin 6) :
      interpolationConstraint (points index) (candidate.eval (points index))
          constraint coefficients = 0 := by
    rw [agreementAt]
    exact interpolationConstraint_eq_zero_of_mem_kernel points values
      coefficients kernel index constraint
  have evalZero : substituted.eval (points index) = 0 := by
    rw [interpolationSubstitute_eval]
    exact constraintZero 0
  have derivativeZero : substituted.derivative.eval (points index) = 0 := by
    rw [interpolationSubstitute_derivative_eval, constraintZero 1,
      constraintZero 2]
    ring
  have secondDerivativeZero :
      (derivative (derivative substituted)).eval (points index) = 0 := by
    rw [interpolationSubstitute_second_derivative_eval, constraintZero 3,
      constraintZero 4, constraintZero 2, constraintZero 5]
    ring
  have taylorCoeffZero : ∀ degree < 3,
      (Polynomial.taylor (points index) substituted).coeff degree = 0 := by
    intro degree degree_lt
    interval_cases degree
    · simpa using evalZero
    · simpa using derivativeZero
    · have doubled := two_mul_taylor_coeff_two substituted (points index)
      rw [secondDerivativeZero] at doubled
      exact mul_left_cancel₀ (NeZero.ne (2 : K)) (by simpa using doubled)
  have xCubeDivides : X ^ 3 ∣ Polynomial.taylor (points index) substituted :=
    Polynomial.X_pow_dvd_iff.mpr taylorCoeffZero
  obtain ⟨quotient, quotientIdentity⟩ := xCubeDivides
  refine ⟨Polynomial.taylor (-(points index)) quotient, ?_⟩
  have shiftedBack := congrArg (Polynomial.taylor (-(points index)))
    quotientIdentity
  simpa [sub_eq_add_neg, Polynomial.taylor_taylor, Polynomial.taylor_mul,
    Polynomial.taylor_pow, add_comm] using shiftedBack

def polynomialAgreementSet
    {K : Type*} [Semiring K] [DecidableEq K] {n : Nat}
    (points values : Fin n → K) (candidate : K[X]) : Finset (Fin n) :=
  Finset.univ.filter fun index => candidate.eval (points index) = values index

@[simp] theorem mem_polynomialAgreementSet
    {K : Type*} [Semiring K] [DecidableEq K] {n : Nat}
    (points values : Fin n → K) (candidate : K[X]) (index : Fin n) :
    index ∈ polynomialAgreementSet points values candidate ↔
      candidate.eval (points index) = values index := by
  simp [polynomialAgreementSet]

/-- Distinct interpolation points with multiplicity-three roots consume three
ordinary roots each, counted with multiplicity. -/
theorem three_mul_agreementCard_le_natDegree
    {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]
    {n maximumDegree weightedDegree ell : Nat}
    (points values : Fin n → K) (pointsInjective : Function.Injective points)
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (kernel : interpolationMap points values coefficients = 0)
    (candidate : K[X])
    (substituteNeZero : interpolationSubstitute coefficients candidate ≠ 0) :
    3 * (polynomialAgreementSet points values candidate).card ≤
      (interpolationSubstitute coefficients candidate).natDegree := by
  classical
  let agreement := polynomialAgreementSet points values candidate
  let rootsAtAgreement := agreement.image points
  have imageCard : rootsAtAgreement.card = agreement.card := by
    exact Finset.card_image_iff.mpr fun left leftMem right rightMem equal =>
      pointsInjective equal
  have countAtLeastThree (root : K) (rootMem : root ∈ rootsAtAgreement) :
      3 ≤ (interpolationSubstitute coefficients candidate).roots.count root := by
    rw [Finset.mem_image] at rootMem
    obtain ⟨index, indexMem, rfl⟩ := rootMem
    rw [Polynomial.count_roots,
      Polynomial.le_rootMultiplicity_iff substituteNeZero]
    apply interpolationMultiplicityThree_dvd points values coefficients kernel
      candidate index
    exact (mem_polynomialAgreementSet points values candidate index).mp indexMem
  have imageSubsetRoots :
      rootsAtAgreement ⊆
        (interpolationSubstitute coefficients candidate).roots.toFinset := by
    intro root rootMem
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]
    exact lt_of_lt_of_le (by norm_num) (countAtLeastThree root rootMem)
  calc
    3 * agreement.card = ∑ _root ∈ rootsAtAgreement, 3 := by
      simp [imageCard, Nat.mul_comm]
    _ ≤ ∑ root ∈ rootsAtAgreement,
        (interpolationSubstitute coefficients candidate).roots.count root := by
      gcongr with root rootMem
      exact countAtLeastThree root rootMem
    _ ≤ ∑ root ∈
        (interpolationSubstitute coefficients candidate).roots.toFinset,
          (interpolationSubstitute coefficients candidate).roots.count root := by
      exact Finset.sum_le_sum_of_subset_of_nonneg imageSubsetRoots
        (fun _ _ _ => Nat.zero_le _)
    _ = (interpolationSubstitute coefficients candidate).roots.card :=
      Multiset.toFinset_sum_count_eq _
    _ ≤ (interpolationSubstitute coefficients candidate).natDegree :=
      Polynomial.card_roots' _

/-- GS root forcing: if the interpolation polynomial has weighted degree
strictly below three times the agreement threshold, every sufficiently close
bounded-degree candidate satisfies the polynomial identity `Q(X,f(X))=0`. -/
theorem interpolationSubstitute_eq_zero_of_agreement
    {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]
    {n maximumDegree weightedDegree ell threshold : Nat}
    (points values : Fin n → K) (pointsInjective : Function.Injective points)
    (coefficients :
      WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (kernel : interpolationMap points values coefficients = 0)
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (rootBudget : weightedDegree < 3 * threshold)
    (candidate : K[X]) (candidateDegree : candidate.natDegree ≤ maximumDegree)
    (agreement : threshold ≤
      (polynomialAgreementSet points values candidate).card) :
    interpolationSubstitute coefficients candidate = 0 := by
  by_contra substituteNeZero
  have rootsBound := three_mul_agreementCard_le_natDegree points values
    pointsInjective coefficients kernel candidate substituteNeZero
  have degreeBound := interpolationSubstitute_natDegree_le lastRow coefficients
    candidate candidateDegree
  omega

/-! ## Exact final-instance root completeness -/

theorem exactFinalPolynomialAgreement_card_eq
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact)
    (message : AspisPool.AlgorithmicCircleDecoderV7.FinalMessage QM31Exact) :
    (polynomialAgreementSet exactFinalGRSConversion.points received
      (exactFinalGRSConversion.messagePolynomial message)).card =
      agreementCount received (exactFinalGRSConversion.grsEncoder message) := by
  unfold polynomialAgreementSet agreementCount ExactGRSConversion.grsEncoder
    generalizedReedSolomonEncode
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro index _
  simp [exactFinalGRSConversion, eq_comm]

/-- Every final V7 polynomial meeting the exact threshold is a root of every
nonzero multiplicity-three interpolation solution selected for that received
word. -/
theorem exactFinalCloseCandidate_substitute_eq_zero
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact)
    (coefficients :
      WeightedMonomialIndex 255 finalWeightedDegree yDegree → QM31Exact)
    (kernel : interpolationMap exactFinalGRSConversion.points received
      coefficients = 0)
    (message : AspisPool.AlgorithmicCircleDecoderV7.FinalMessage QM31Exact)
    (close : closeAtLeast 9558 exactFinalGRSConversion.grsEncoder received
      message) :
    interpolationSubstitute coefficients
      (exactFinalGRSConversion.messagePolynomial message) = 0 := by
  apply interpolationSubstitute_eq_zero_of_agreement
    exactFinalGRSConversion.points received
    exactFinalGRSConversion.points_injective coefficients kernel
    exactFinalInterpolationBudget.2.2.2.1
    exactFinalInterpolationBudget.2.2.1
    (exactFinalGRSConversion.messagePolynomial message)
    (exactFinalGRSConversion.messagePolynomial_degree_le message)
  unfold closeAtLeast at close
  rw [exactFinalPolynomialAgreement_card_eq]
  exact close

/-! ## Exact initial-instance root completeness -/

/-- Divide the received initial word by the proved nonzero GRS column
multiplier before ordinary polynomial interpolation. -/
def exactInitialNormalizedReceived
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    Fin 1048576 → QM31Exact := fun index =>
  (exactInitialGRSConversion.multipliers index)⁻¹ * received index

/-- Agreement with the normalized polynomial evaluations is exactly agreement
with the concrete initial GRS word, including its nontrivial column
multipliers. -/
theorem exactInitialPolynomialAgreement_card_eq
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (message : AspisPool.AlgorithmicCircleDecoderV7.InitialMessage QM31Exact) :
    (polynomialAgreementSet exactInitialGRSConversion.points
      (exactInitialNormalizedReceived received)
      (exactInitialGRSConversion.messagePolynomial message)).card =
      agreementCount received (exactInitialGRSConversion.grsEncoder message) := by
  unfold polynomialAgreementSet agreementCount ExactGRSConversion.grsEncoder
    generalizedReedSolomonEncode exactInitialNormalizedReceived
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro index _
  have multiplierNeZero :=
    exactInitialGRSConversion.multipliers_ne_zero index
  rw [eq_inv_mul_iff_mul_eq₀ multiplierNeZero]
  exact eq_comm

/-- Every initial V7 message meeting the exact threshold makes the selected
multiplicity-three interpolant vanish after substitution.  This uses the
released 1024-dimensional message image inside the ambient degree-at-most-1024
GRS code; no surjectivity onto the 1025-dimensional ambient space is claimed. -/
theorem exactInitialCloseCandidate_substitute_eq_zero
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (coefficients :
      WeightedMonomialIndex 1024 initialWeightedDegree yDegree → QM31Exact)
    (kernel : interpolationMap exactInitialGRSConversion.points
      (exactInitialNormalizedReceived received) coefficients = 0)
    (message : AspisPool.AlgorithmicCircleDecoderV7.InitialMessage QM31Exact)
    (close : closeAtLeast 38230 exactInitialGRSConversion.grsEncoder received
      message) :
    interpolationSubstitute coefficients
      (exactInitialGRSConversion.messagePolynomial message) = 0 := by
  apply interpolationSubstitute_eq_zero_of_agreement
    exactInitialGRSConversion.points (exactInitialNormalizedReceived received)
    exactInitialGRSConversion.points_injective coefficients kernel
    exactInitialInterpolationBudget.2.2.2.1
    exactInitialInterpolationBudget.2.2.1
    (exactInitialGRSConversion.messagePolynomial message)
    (exactInitialGRSConversion.messagePolynomial_degree_le message)
  unfold closeAtLeast at close
  rw [exactInitialPolynomialAgreement_card_eq]
  exact close

/-- Dimension counting produces a nonzero interpolation coefficient vector
whenever the weighted monomial count exceeds the six constraints per point.
This is the linear-algebra existence step of multiplicity-three GS. -/
theorem exists_nonzero_interpolationKernel
    {K : Type*} [Field K]
    {n maximumDegree weightedDegree ell : Nat}
    (points values : Fin n → K)
    (dimension : 6 * n <
      weightedMonomialCount maximumDegree weightedDegree ell) :
    ∃ coefficients :
        WeightedMonomialIndex maximumDegree weightedDegree ell → K,
      coefficients ≠ 0 ∧
        interpolationMap points values coefficients = 0 := by
  let constraints := interpolationMap
    (maximumDegree := maximumDegree) (weightedDegree := weightedDegree)
    (ell := ell) points values
  have finrank_lt :
      Module.finrank K (Fin n → Fin 6 → K) <
        Module.finrank K
          (WeightedMonomialIndex maximumDegree weightedDegree ell → K) := by
    rw [Module.finrank_pi_fintype, Module.finrank_pi,
      Module.finrank_pi, weightedMonomialIndex_card]
    simpa [mul_comm] using dimension
  have kernel_ne_bottom : LinearMap.ker constraints ≠ ⊥ :=
    constraints.ker_ne_bot_of_finrank_lt finrank_lt
  rw [Submodule.ne_bot_iff] at kernel_ne_bottom
  obtain ⟨coefficients, coefficients_mem, coefficients_ne_zero⟩ :=
    kernel_ne_bottom
  exact ⟨coefficients, coefficients_ne_zero,
    LinearMap.mem_ker.mp coefficients_mem⟩

/-- The exact final V7 interpolation system has a nonzero solution for every
received word, before any agreement hypothesis is made. -/
theorem exists_exactFinalInterpolation
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    ∃ coefficients :
        WeightedMonomialIndex 255 finalWeightedDegree yDegree → QM31Exact,
      coefficients ≠ 0 ∧
        interpolationMap exactFinalGRSConversion.points received coefficients =
          0 := by
  apply exists_nonzero_interpolationKernel
  exact exactFinalInterpolationBudget.2.1

/-- The exact initial interpolation system uses received symbols normalized
by the proved nonzero GRS column multipliers. -/
theorem exists_exactInitialInterpolation
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    ∃ coefficients :
        WeightedMonomialIndex 1024 initialWeightedDegree yDegree → QM31Exact,
      coefficients ≠ 0 ∧
        interpolationMap exactInitialGRSConversion.points
          (fun index =>
            (exactInitialGRSConversion.multipliers index)⁻¹ * received index)
          coefficients = 0 := by
  apply exists_nonzero_interpolationKernel
  exact exactInitialInterpolationBudget.2.1

/-! ## Deterministic final-instance decoder -/

/-- A fixed interpolation solution for each received word.  `Classical.choose`
chooses one value once and for all; subsequent candidate production is a
single-valued deterministic function of the received word. -/
noncomputable def exactFinalInterpolationCoefficients
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    WeightedMonomialIndex 255 finalWeightedDegree yDegree → QM31Exact :=
  Classical.choose (exists_exactFinalInterpolation received)

theorem exactFinalInterpolationCoefficients_ne_zero
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    exactFinalInterpolationCoefficients received ≠ 0 :=
  (Classical.choose_spec (exists_exactFinalInterpolation received)).1

set_option maxHeartbeats 800000 in
theorem exactFinalInterpolationCoefficients_kernel
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    interpolationMap exactFinalGRSConversion.points received
      (exactFinalInterpolationCoefficients received) = 0 :=
  (Classical.choose_spec (exists_exactFinalInterpolation received)).2

/-- The factor-candidate stage: enumerate exactly the released degree-255
message polynomials satisfying `Q(X,f(X)) = 0`.  This finite definition makes
candidate production deterministic; its membership proof is the GS
root-completeness theorem above, not an assumed factorization oracle. -/
noncomputable def exactFinalRootCandidates
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    Finset (FinalMessage QM31Exact) := by
  classical
  exact Finset.univ.filter fun message =>
    interpolationSubstitute (exactFinalInterpolationCoefficients received)
      (exactFinalGRSConversion.messagePolynomial message) = 0

noncomputable def exactFinalCloseCandidates
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    Finset (FinalMessage QM31Exact) := by
  classical
  exact Finset.univ.filter fun message =>
    closeAtLeast 9558
      AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder
      received message

theorem exactFinalRootCandidates_mem_iff
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact)
    (message : FinalMessage QM31Exact) :
    message ∈ exactFinalRootCandidates received ↔
      interpolationSubstitute (exactFinalInterpolationCoefficients received)
        (exactFinalGRSConversion.messagePolynomial message) = 0 := by
  classical
  simp only [exactFinalRootCandidates, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- Sound candidate list: retain only roots that actually meet the released
V7 agreement threshold. -/
noncomputable def exactFinalDecodedCandidates
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    Finset (FinalMessage QM31Exact) := by
  classical
  exact Finset.univ.filter fun message =>
    interpolationSubstitute (exactFinalInterpolationCoefficients received)
        (exactFinalGRSConversion.messagePolynomial message) = 0 ∧
      closeAtLeast 9558
        AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder
        received message

noncomputable def exactFinalGSDecode
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    List (FinalMessage QM31Exact) :=
  (exactFinalDecodedCandidates received).toList

set_option maxRecDepth 8192 in
theorem exactFinalRootCandidates_complete
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact)
    (message : FinalMessage QM31Exact)
    (close : closeAtLeast 9558
      AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder
      received message) :
    message ∈ exactFinalRootCandidates received := by
  classical
  simp only [exactFinalRootCandidates, Finset.mem_filter, Finset.mem_univ,
    true_and]
  apply exactFinalCloseCandidate_substitute_eq_zero received
    (exactFinalInterpolationCoefficients received)
    (exactFinalInterpolationCoefficients_kernel received) message
  exact (exactFinal9558_transport received message).mp close

/-- Exact completeness and soundness of the deterministic final decoder. -/
theorem exactFinalGSDecode_mem_iff
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact)
    (message : FinalMessage QM31Exact) :
    message ∈ exactFinalGSDecode received ↔
      closeAtLeast 9558
        AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder
        received message := by
  classical
  simp only [exactFinalGSDecode, Finset.mem_toList,
    exactFinalDecodedCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro close
    refine ⟨?_, close⟩
    apply exactFinalCloseCandidate_substitute_eq_zero received
      (exactFinalInterpolationCoefficients received)
      (exactFinalInterpolationCoefficients_kernel received) message
    exact (exactFinal9558_transport received message).mp close

theorem exactFinalGSDecode_nodup
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    (exactFinalGSDecode received).Nodup := by
  exact Finset.nodup_toList _

theorem exactFinalDecodedCandidates_eq_closeFilter
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    exactFinalDecodedCandidates received = exactFinalCloseCandidates received := by
  classical
  ext message
  simp only [exactFinalDecodedCandidates, exactFinalCloseCandidates,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro close
    refine ⟨?_, close⟩
    apply exactFinalCloseCandidate_substitute_eq_zero received
      (exactFinalInterpolationCoefficients received)
      (exactFinalInterpolationCoefficients_kernel received) message
    exact (exactFinal9558_transport received message).mp close

/-- The subtype of released final messages meeting the exact V7 threshold. -/
abbrev ExactFinalCloseCandidate
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :=
  { message : FinalMessage QM31Exact //
    closeAtLeast 9558
      AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder
      received message }

/-- The exact final close-message set contains fewer than 100 messages, hence
at most the published list-size cap of 99. -/
theorem exactFinalCloseCandidate_card_lt_100
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    Nat.card (ExactFinalCloseCandidate received) < 100 := by
  classical
  letI : Fintype (ExactFinalCloseCandidate received) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  let candidateAgreement : ExactFinalCloseCandidate received →
      Finset (Fin 262144) := fun candidate =>
    AspisV5FriCoherentCandidateExtraction.agreementSet received
      (AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder
        candidate.1)
  apply AspisV6OneFoldParameterAudit.output_list_card_lt_100
    candidateAgreement
  · intro candidate
    simpa only [candidateAgreement, closeAtLeast, agreementCount,
      AspisV5FriCoherentCandidateExtraction.agreementSet] using
      candidate.property
  · intro left right different
    have messagesDifferent : left.1 ≠ right.1 := by
      intro equal
      apply different
      exact Subtype.ext equal
    apply (Finset.card_le_card ?_).trans
      (AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder_overlap_cap
        left.1 right.1 messagesDifferent)
    intro index indexMem
    simp only [candidateAgreement,
      AspisV5FriCoherentCandidateExtraction.agreementSet,
      Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      at indexMem ⊢
    exact indexMem.1.symm.trans indexMem.2

/-- Exact published list-size bound for the deterministic final decoder. -/
theorem exactFinalGSDecode_length_le_99
    (received : AspisPool.AlgorithmicCircleDecoderV7.FinalWord QM31Exact) :
    (exactFinalGSDecode received).length ≤ 99 := by
  classical
  letI : Fintype (ExactFinalCloseCandidate received) := Fintype.ofFinite _
  have bounded : Fintype.card (ExactFinalCloseCandidate received) < 100 := by
    simpa only [Nat.card_eq_fintype_card] using
      exactFinalCloseCandidate_card_lt_100 received
  rw [Fintype.card_subtype] at bounded
  rw [exactFinalGSDecode, Finset.length_toList,
    exactFinalDecodedCandidates_eq_closeFilter]
  rw [exactFinalCloseCandidates]
  omega

/-! ## Deterministic initial-instance decoder -/

noncomputable def exactInitialInterpolationCoefficients
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    WeightedMonomialIndex 1024 initialWeightedDegree yDegree → QM31Exact :=
  Classical.choose (exists_exactInitialInterpolation received)

theorem exactInitialInterpolationCoefficients_ne_zero
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    exactInitialInterpolationCoefficients received ≠ 0 :=
  (Classical.choose_spec (exists_exactInitialInterpolation received)).1

set_option maxHeartbeats 800000 in
theorem exactInitialInterpolationCoefficients_kernel
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    interpolationMap exactInitialGRSConversion.points
      (exactInitialNormalizedReceived received)
      (exactInitialInterpolationCoefficients received) = 0 :=
  (Classical.choose_spec (exists_exactInitialInterpolation received)).2

noncomputable def exactInitialRootCandidates
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    Finset (InitialMessage QM31Exact) := by
  classical
  exact Finset.univ.filter fun message =>
    interpolationSubstitute (exactInitialInterpolationCoefficients received)
      (exactInitialGRSConversion.messagePolynomial message) = 0

noncomputable def exactInitialCloseCandidates
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    Finset (InitialMessage QM31Exact) := by
  classical
  exact Finset.univ.filter fun message =>
    closeAtLeast 38230
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder
      received message

theorem exactInitialRootCandidates_mem_iff
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (message : InitialMessage QM31Exact) :
    message ∈ exactInitialRootCandidates received ↔
      interpolationSubstitute (exactInitialInterpolationCoefficients received)
        (exactInitialGRSConversion.messagePolynomial message) = 0 := by
  classical
  simp only [exactInitialRootCandidates, Finset.mem_filter, Finset.mem_univ,
    true_and]

noncomputable def exactInitialDecodedCandidates
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    Finset (InitialMessage QM31Exact) := by
  classical
  exact Finset.univ.filter fun message =>
    interpolationSubstitute (exactInitialInterpolationCoefficients received)
        (exactInitialGRSConversion.messagePolynomial message) = 0 ∧
      closeAtLeast 38230
        AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder
        received message

noncomputable def exactInitialGSDecode
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    List (InitialMessage QM31Exact) :=
  (exactInitialDecodedCandidates received).toList

set_option maxRecDepth 8192 in
theorem exactInitialRootCandidates_complete
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (message : InitialMessage QM31Exact)
    (close : closeAtLeast 38230
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder
      received message) :
    message ∈ exactInitialRootCandidates received := by
  classical
  simp only [exactInitialRootCandidates, Finset.mem_filter, Finset.mem_univ,
    true_and]
  apply exactInitialCloseCandidate_substitute_eq_zero received
    (exactInitialInterpolationCoefficients received)
    (exactInitialInterpolationCoefficients_kernel received) message
  exact (exactInitial38230_transport received message).mp close

/-- Exact completeness and soundness of the deterministic initial decoder. -/
theorem exactInitialGSDecode_mem_iff
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact)
    (message : InitialMessage QM31Exact) :
    message ∈ exactInitialGSDecode received ↔
      closeAtLeast 38230
        AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder
        received message := by
  classical
  simp only [exactInitialGSDecode, Finset.mem_toList,
    exactInitialDecodedCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro close
    refine ⟨?_, close⟩
    apply exactInitialCloseCandidate_substitute_eq_zero received
      (exactInitialInterpolationCoefficients received)
      (exactInitialInterpolationCoefficients_kernel received) message
    exact (exactInitial38230_transport received message).mp close

theorem exactInitialGSDecode_nodup
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    (exactInitialGSDecode received).Nodup := by
  exact Finset.nodup_toList _

theorem exactInitialDecodedCandidates_eq_closeFilter
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    exactInitialDecodedCandidates received =
      exactInitialCloseCandidates received := by
  classical
  ext message
  simp only [exactInitialDecodedCandidates, exactInitialCloseCandidates,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro close
    refine ⟨?_, close⟩
    apply exactInitialCloseCandidate_substitute_eq_zero received
      (exactInitialInterpolationCoefficients received)
      (exactInitialInterpolationCoefficients_kernel received) message
    exact (exactInitial38230_transport received message).mp close

abbrev ExactInitialCloseCandidate
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :=
  { message : InitialMessage QM31Exact //
    closeAtLeast 38230
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder
      received message }

/-- The exact initial released-message subcode contains fewer than 101 close
messages, hence at most the published list-size cap of 100. -/
theorem exactInitialCloseCandidate_card_lt_101
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    Nat.card (ExactInitialCloseCandidate received) < 101 := by
  classical
  letI : Fintype (ExactInitialCloseCandidate received) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  let candidateAgreement : ExactInitialCloseCandidate received →
      Finset (Fin 1048576) := fun candidate =>
    AspisV5FriCoherentCandidateExtraction.agreementSet received
      (AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder candidate.1)
  apply AspisV6OneFoldParameterAudit.initial_list_card_lt_101
    candidateAgreement
  · intro candidate
    simpa only [candidateAgreement, closeAtLeast, agreementCount,
      AspisV5FriCoherentCandidateExtraction.agreementSet] using
      candidate.property
  · intro left right different
    have messagesDifferent : left.1 ≠ right.1 := by
      intro equal
      apply different
      exact Subtype.ext equal
    have overlapCap :
        (AspisV5FriCoherentCandidateExtraction.agreementSet
          (AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder left.1)
          (AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder right.1)).card
          ≤ 1024 := by
      simpa only [agreementCount,
        AspisV5FriCoherentCandidateExtraction.agreementSet] using
        AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder_overlap_cap
          left.1 right.1 messagesDifferent
    apply (Finset.card_le_card ?_).trans overlapCap
    intro index indexMem
    simp only [candidateAgreement,
      AspisV5FriCoherentCandidateExtraction.agreementSet,
      Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      at indexMem ⊢
    exact indexMem.1.symm.trans indexMem.2

/-- Exact published list-size bound for the deterministic initial decoder. -/
theorem exactInitialGSDecode_length_le_100
    (received : AspisPool.AlgorithmicCircleDecoderV7.InitialWord QM31Exact) :
    (exactInitialGSDecode received).length ≤ 100 := by
  classical
  letI : Fintype (ExactInitialCloseCandidate received) := Fintype.ofFinite _
  have bounded : Fintype.card (ExactInitialCloseCandidate received) < 101 := by
    simpa only [Nat.card_eq_fintype_card] using
      exactInitialCloseCandidate_card_lt_101 received
  rw [Fintype.card_subtype] at bounded
  rw [exactInitialGSDecode, Finset.length_toList,
    exactInitialDecodedCandidates_eq_closeFilter]
  rw [exactInitialCloseCandidates]
  omega

/-! ## Reviewable exact decoder boundary -/

/-- Mathematical data and kernel proofs supplied by an exact
multiplicity-three interpolation decoder.  The structure deliberately does
not contain a bare "GS applies" proposition: it exposes the interpolant,
factor candidates, exact decoder membership, and list bound. -/
structure ExactMultiplicityThreeGSBoundary
    (K Message : Type*) [Field K] [DecidableEq K]
    (n maximumDegree weightedDegree ell threshold listSizeCap : Nat)
    (encoder : Message → Fin n → K)
    (points : Fin n → K)
    (normalizeReceived : (Fin n → K) → Fin n → K)
    (messagePolynomial : Message → K[X]) where
  points_injective : Function.Injective points
  messagePolynomial_degree_le : ∀ message,
    (messagePolynomial message).natDegree ≤ maximumDegree
  interpolationCoefficients :
    (received : Fin n → K) →
      WeightedMonomialIndex maximumDegree weightedDegree ell → K
  interpolationCoefficients_ne_zero : ∀ received,
    interpolationCoefficients received ≠ 0
  interpolationKernel : ∀ received,
    interpolationMap points (normalizeReceived received)
      (interpolationCoefficients received) = 0
  rootCandidates : (Fin n → K) → Finset Message
  rootCandidates_mem_iff : ∀ received message,
    message ∈ rootCandidates received ↔
      interpolationSubstitute (interpolationCoefficients received)
        (messagePolynomial message) = 0
  decode : (Fin n → K) → List Message
  decode_nodup : ∀ received, (decode received).Nodup
  decode_mem_iff : ∀ received message,
    message ∈ decode received ↔
      closeAtLeast threshold encoder received message
  outputBound : ∀ received, (decode received).length ≤ listSizeCap

/-- Complete exact multiplicity-three GS boundary for the released final
`256 → 2^18` V7 GRS code at threshold `9558` and list cap `99`. -/
noncomputable def exactFinalMultiplicityThreeGS :
    ExactMultiplicityThreeGSBoundary QM31Exact (FinalMessage QM31Exact)
      262144 255 finalWeightedDegree yDegree 9558 99
      AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder
      exactFinalGRSConversion.points (fun received => received)
      exactFinalGRSConversion.messagePolynomial where
  points_injective := exactFinalGRSConversion.points_injective
  messagePolynomial_degree_le :=
    exactFinalGRSConversion.messagePolynomial_degree_le
  interpolationCoefficients := exactFinalInterpolationCoefficients
  interpolationCoefficients_ne_zero :=
    exactFinalInterpolationCoefficients_ne_zero
  interpolationKernel := exactFinalInterpolationCoefficients_kernel
  rootCandidates := exactFinalRootCandidates
  rootCandidates_mem_iff := exactFinalRootCandidates_mem_iff
  decode := exactFinalGSDecode
  decode_nodup := exactFinalGSDecode_nodup
  decode_mem_iff := exactFinalGSDecode_mem_iff
  outputBound := exactFinalGSDecode_length_le_99

/-- Complete exact multiplicity-three GS boundary for the released initial
`1024 → 2^20` V7 GRS subcode at threshold `38230` and list cap `100`. -/
noncomputable def exactInitialMultiplicityThreeGS :
    ExactMultiplicityThreeGSBoundary QM31Exact (InitialMessage QM31Exact)
      1048576 1024 initialWeightedDegree yDegree 38230 100
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder
      exactInitialGRSConversion.points exactInitialNormalizedReceived
      exactInitialGRSConversion.messagePolynomial where
  points_injective := exactInitialGRSConversion.points_injective
  messagePolynomial_degree_le :=
    exactInitialGRSConversion.messagePolynomial_degree_le
  interpolationCoefficients := exactInitialInterpolationCoefficients
  interpolationCoefficients_ne_zero :=
    exactInitialInterpolationCoefficients_ne_zero
  interpolationKernel := exactInitialInterpolationCoefficients_kernel
  rootCandidates := exactInitialRootCandidates
  rootCandidates_mem_iff := exactInitialRootCandidates_mem_iff
  decode := exactInitialGSDecode
  decode_nodup := exactInitialGSDecode_nodup
  decode_mem_iff := exactInitialGSDecode_mem_iff
  outputBound := exactInitialGSDecode_length_le_100

end

#print axioms exactInitialAmbientDegreeConvention
#print axioms exactFinalAmbientDegreeConvention
#print axioms exactFinalInterpolationBudget
#print axioms exactInitialInterpolationBudget
#print axioms exists_nonzero_interpolationKernel
#print axioms exists_exactFinalInterpolation
#print axioms exists_exactInitialInterpolation
#print axioms interpolationMultiplicityThree_dvd
#print axioms interpolationSubstitute_eq_zero_of_agreement
#print axioms exactFinalPolynomialAgreement_card_eq
#print axioms exactFinalRootCandidates_complete
#print axioms exactFinalGSDecode_mem_iff
#print axioms exactFinalGSDecode_length_le_99
#print axioms exactFinalMultiplicityThreeGS
#print axioms exactInitialPolynomialAgreement_card_eq
#print axioms exactInitialRootCandidates_complete
#print axioms exactInitialGSDecode_mem_iff
#print axioms exactInitialGSDecode_length_le_100
#print axioms exactInitialMultiplicityThreeGS

end AspisK1.V7Tag73ExactMultiplicityThreeGS
