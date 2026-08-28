import AspisFormal.K1.V7ExactCorrelatedAgreementRegularZeroCount
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Denominator arithmetic for the exact V7 Hensel lift

For the coefficient of order `t`, the characteristic-free implicit-function
recurrence uses denominator exponent `max 0 (2t-1)`.  Products are indexed by
the literal finite antidiagonals occurring in `PowerSeries.coeff_pow`.  The
lemmas here prove the exact exponent accounting; in particular, nonlinear
terms have at least two positive parts and save two denominator powers.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics

open scoped BigOperators
open Finset (antidiagonal mem_antidiagonal)

/-- The denominator exponent from BCIKS Claim A.2.  Natural subtraction makes
the `t=0` case definitionally zero. -/
def henselDenominatorExponent (t : Nat) : Nat := 2 * t - 1

@[simp] theorem henselDenominatorExponent_zero :
    henselDenominatorExponent 0 = 0 := by
  simp [henselDenominatorExponent]

theorem henselDenominatorExponent_of_pos
    (t : Nat) (tPositive : 0 < t) :
    henselDenominatorExponent t + 1 = 2 * t := by
  unfold henselDenominatorExponent
  omega

/-- Number of genuinely positive coefficient indices in one convolution
tuple. -/
def positivePartCount (indices : Finset Nat) (parts : Nat →₀ Nat) : Nat :=
  (indices.filter fun index => parts index ≠ 0).card

/-- Exact denominator identity on any finite convolution tuple. -/
theorem sum_henselDenominatorExponent_add_positivePartCount
    (indices : Finset Nat) (parts : Nat →₀ Nat) :
    (∑ index ∈ indices, henselDenominatorExponent (parts index)) +
        positivePartCount indices parts =
      2 * ∑ index ∈ indices, parts index := by
  classical
  unfold positivePartCount
  rw [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ index ∈ indices,
        (henselDenominatorExponent (parts index) +
          if parts index ≠ 0 then 1 else 0) =
        ∑ index ∈ indices, 2 * parts index := by
      apply Finset.sum_congr rfl
      intro index _
      by_cases partZero : parts index = 0
      · simp [partZero]
      · rw [if_pos partZero]
        exact henselDenominatorExponent_of_pos _ (Nat.pos_of_ne_zero partZero)
    _ = 2 * ∑ index ∈ indices, parts index := by
      rw [Finset.mul_sum]

/-- Every positive-total antidiagonal term saves at least one power. -/
theorem sum_henselDenominatorExponent_le_two_mul_sub_one
    (indices : Finset Nat) (parts : Nat →₀ Nat) (total : Nat)
    (partsSum : ∑ index ∈ indices, parts index = total)
    (totalPositive : 0 < total) :
    ∑ index ∈ indices, henselDenominatorExponent (parts index) ≤
      2 * total - 1 := by
  have somePositive : 0 < positivePartCount indices parts := by
    by_contra noPositive
    have countZero : positivePartCount indices parts = 0 := by omega
    have allZero : ∀ index ∈ indices, parts index = 0 := by
      intro index indexMem
      by_contra partNeZero
      have filteredMem : index ∈ indices.filter fun other => parts other ≠ 0 :=
        Finset.mem_filter.mpr ⟨indexMem, partNeZero⟩
      have cardPositive : 0 <
          (indices.filter fun other => parts other ≠ 0).card :=
        Finset.card_pos.mpr ⟨index, filteredMem⟩
      exact (Nat.ne_of_gt cardPositive) countZero
    have sumZero : ∑ index ∈ indices, parts index = 0 := by
      exact Finset.sum_eq_zero fun index indexMem => allZero index indexMem
    rw [sumZero] at partsSum
    omega
  have identity :=
    sum_henselDenominatorExponent_add_positivePartCount indices parts
  rw [partsSum] at identity
  omega

/-- A nonlinear convolution term (at least two positive coefficient
indices) saves two denominator powers. -/
theorem sum_henselDenominatorExponent_le_two_mul_sub_two
    (indices : Finset Nat) (parts : Nat →₀ Nat) (total : Nat)
    (partsSum : ∑ index ∈ indices, parts index = total)
    (twoPositiveParts : 2 ≤ positivePartCount indices parts) :
    ∑ index ∈ indices, henselDenominatorExponent (parts index) ≤
      2 * total - 2 := by
  have identity :=
    sum_henselDenominatorExponent_add_positivePartCount indices parts
  rw [partsSum] at identity
  omega

/-- A denominator tuple never uses more than twice its total order.  This
coarser form also covers the all-zero tuple and is the convenient bound for
positive shifted-`X` coefficients. -/
theorem sum_henselDenominatorExponent_le_two_mul
    (indices : Finset Nat) (parts : Nat →₀ Nat) (total : Nat)
    (partsSum : ∑ index ∈ indices, parts index = total) :
    ∑ index ∈ indices, henselDenominatorExponent (parts index) ≤
      2 * total := by
  have identity :=
    sum_henselDenominatorExponent_add_positivePartCount indices parts
  rw [partsSum] at identity
  omega

/-- If a convolution consumes strictly less than the target order, all of
its denominator exponents fit below `e_target - 1`.  This is exactly the
extra `eta` power made available after applying the implicit recurrence. -/
theorem sum_henselDenominatorExponent_le_target_sub_one_of_total_lt
    (indices : Finset Nat) (parts : Nat →₀ Nat)
    (subOrder targetOrder : Nat)
    (partsSum : ∑ index ∈ indices, parts index = subOrder)
    (subOrderLt : subOrder < targetOrder) :
    ∑ index ∈ indices, henselDenominatorExponent (parts index) ≤
      henselDenominatorExponent targetOrder - 1 := by
  have bounded := sum_henselDenominatorExponent_le_two_mul indices parts
    subOrder partsSum
  have targetPositive : 0 < targetOrder := by omega
  have targetExponent : henselDenominatorExponent targetOrder - 1 =
      2 * targetOrder - 2 := by
    unfold henselDenominatorExponent
    omega
  rw [targetExponent]
  omega

/-! ## Denominator-clearing product identity -/

/-- Clear one `W` and `eta^e_i` from every factor of a convolution product.
The remaining powers are explicit natural subtractions justified by the two
input inequalities; no field division or cancellation is used. -/
theorem clear_hensel_product_denominators
    {R ι : Type*} [CommMonoid R] (indices : Finset ι)
    (leading eta : R) (exponent : ι → Nat) (value : ι → R)
    (leadingPower etaPower : Nat)
    (cardLe : indices.card ≤ leadingPower)
    (sumLe : ∑ index ∈ indices, exponent index ≤ etaPower) :
    leading ^ leadingPower * eta ^ etaPower *
        (∏ index ∈ indices, value index) =
      leading ^ (leadingPower - indices.card) *
        eta ^ (etaPower - ∑ index ∈ indices, exponent index) *
          (∏ index ∈ indices,
            (leading * eta ^ exponent index) * value index) := by
  classical
  symm
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  let exponentSum := ∑ index ∈ indices, exponent index
  have leadingExponent : leadingPower - indices.card + indices.card =
      leadingPower := Nat.sub_add_cancel cardLe
  have etaExponent : etaPower - exponentSum + exponentSum = etaPower :=
    Nat.sub_add_cancel sumLe
  calc
    leading ^ (leadingPower - indices.card) *
          eta ^ (etaPower - exponentSum) *
          ((leading ^ indices.card * eta ^ exponentSum) *
            ∏ x ∈ indices, value x) =
        (leading ^ (leadingPower - indices.card) *
            leading ^ indices.card) *
          (eta ^ (etaPower - exponentSum) * eta ^ exponentSum) *
            ∏ x ∈ indices, value x := by ac_rfl
    _ = leading ^ leadingPower * eta ^ etaPower *
          ∏ x ∈ indices, value x := by
      rw [← pow_add, leadingExponent, ← pow_add, etaExponent]

/-- In a `PowerSeries.coeff_pow` antidiagonal, a tuple with at most one
positive part is exactly the linear occurrence: one index carries the whole
positive order and every other index is zero. -/
theorem exists_unique_full_part_of_positivePartCount_eq_one
    (indices : Finset Nat) (parts : Nat →₀ Nat) (total : Nat)
    (partsSum : ∑ index ∈ indices, parts index = total)
    (onePositive : positivePartCount indices parts = 1) :
    ∃! index, index ∈ indices ∧ parts index = total := by
  classical
  have singleton : ∃ index,
      indices.filter (fun other => parts other ≠ 0) = {index} :=
    Finset.card_eq_one.mp onePositive
  obtain ⟨index, filteredEq⟩ := singleton
  have indexFiltered : index ∈
      indices.filter (fun other => parts other ≠ 0) := by
    rw [filteredEq]
    exact Finset.mem_singleton_self index
  have indexMem := (Finset.mem_filter.mp indexFiltered).1
  have otherZero : ∀ other ∈ indices, other ≠ index → parts other = 0 := by
    intro other otherMem otherNe
    by_contra otherNonzero
    have otherFiltered : other ∈
        indices.filter (fun candidate => parts candidate ≠ 0) :=
      Finset.mem_filter.mpr ⟨otherMem, otherNonzero⟩
    rw [filteredEq, Finset.mem_singleton] at otherFiltered
    exact otherNe otherFiltered
  have indexFull : parts index = total := by
    calc
      parts index = ∑ other ∈ indices, parts other := by
        rw [Finset.sum_eq_single index]
        · intro other otherMem otherNe
          exact otherZero other otherMem otherNe
        · intro indexNotMem
          exact (indexNotMem indexMem).elim
      _ = total := partsSum
  refine ⟨index, ⟨indexMem, indexFull⟩, ?_⟩
  intro other otherProperty
  by_contra otherNe
  have totalPositive : 0 < total := by
    have indexNonzero := (Finset.mem_filter.mp indexFiltered).2
    rw [indexFull] at indexNonzero
    exact Nat.pos_of_ne_zero indexNonzero
  have otherNonzero : parts other ≠ 0 := by
    rw [otherProperty.2]
    exact Nat.ne_of_gt totalPositive
  exact otherNonzero (otherZero other otherProperty.1 otherNe)

/-! ## Literal convolution terms from `PowerSeries.coeff_pow` -/

/-- A nonzero coefficient product of a power series with zero constant term
cannot use a zero part.  Consequently every one of the `power` factors is a
genuinely positive part of the convolution tuple. -/
theorem positivePartCount_range_eq_of_coeffProduct_ne_zero
    {R : Type*} [CommRing R] (series : PowerSeries R)
    (constantZero : PowerSeries.constantCoeff series = 0)
    (power : Nat) (parts : Nat →₀ Nat)
    (productNeZero :
      ∏ index ∈ Finset.range power,
        PowerSeries.coeff (parts index) series ≠ 0) :
    positivePartCount (Finset.range power) parts = power := by
  classical
  unfold positivePartCount
  have filterAll :
      (Finset.range power).filter (fun index => parts index ≠ 0) =
        Finset.range power := by
    apply Finset.filter_eq_self.mpr
    intro index indexMem partZero
    apply productNeZero
    apply Finset.prod_eq_zero indexMem
    rw [partZero, PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantZero
  rw [filterAll, Finset.card_range]

/-- Every nonzero nonlinear (`power ≥ 2`) contribution to coefficient
`order` has total denominator exponent at most `2*order-2`. -/
theorem convolution_henselExponent_le_two_mul_sub_two
    {R : Type*} [CommRing R] (series : PowerSeries R)
    (constantZero : PowerSeries.constantCoeff series = 0)
    (power order : Nat) (powerAtLeastTwo : 2 ≤ power)
    (parts : Nat →₀ Nat)
    (partsMem : parts ∈ (Finset.range power).finsuppAntidiag order)
    (productNeZero :
      ∏ index ∈ Finset.range power,
        PowerSeries.coeff (parts index) series ≠ 0) :
    ∑ index ∈ Finset.range power,
        henselDenominatorExponent (parts index) ≤
      2 * order - 2 := by
  have partsSum : ∑ index ∈ Finset.range power, parts index = order :=
    (Finset.mem_finsuppAntidiag.mp partsMem).1
  apply sum_henselDenominatorExponent_le_two_mul_sub_two
    (Finset.range power) parts order partsSum
  rw [positivePartCount_range_eq_of_coeffProduct_ne_zero series
    constantZero power parts productNeZero]
  exact powerAtLeastTwo

/-! ## Separating the unique linear derivative contribution -/

/-- The genuinely nonlinear part of the coefficient of `series^power` at a
positive order.  The summation index is the literal binomial exponent of the
zero-constant part. -/
noncomputable def nonlinearPowerCoefficient
    {R : Type*} [CommRing R] (power order : Nat)
    (series : PowerSeries R) : R :=
  ∑ nonlinearExponent ∈ Finset.Icc 2 power,
    (power.choose nonlinearExponent : R) *
      PowerSeries.constantCoeff series ^ (power - nonlinearExponent) *
        PowerSeries.coeff order
          ((series - PowerSeries.C (PowerSeries.constantCoeff series)) ^
            nonlinearExponent)

/-- At positive order, the coefficient of a power is the unique linear term
`power * a^(power-1) * coeff_order` plus terms containing at least two
positive-order coefficients. -/
theorem coeff_pow_eq_linear_add_nonlinear
    {R : Type*} [CommRing R] (series : PowerSeries R)
    (power order : Nat) (powerPositive : 0 < power)
    (orderPositive : 0 < order) :
    PowerSeries.coeff order (series ^ power) =
      (power : R) * PowerSeries.constantCoeff series ^ (power - 1) *
          PowerSeries.coeff order series +
        nonlinearPowerCoefficient power order series := by
  classical
  let constant := PowerSeries.constantCoeff series
  let tail := series - PowerSeries.C constant
  have seriesDecomposition : tail + PowerSeries.C constant = series := by
    dsimp [tail, constant]
    exact sub_add_cancel _ _
  have rangeDecomposition : Finset.range (power + 1) =
      insert 0 (insert 1 (Finset.Icc 2 power)) := by
    ext exponent
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have expanded := congrArg (PowerSeries.coeff order)
    (add_pow tail (PowerSeries.C constant) power)
  rw [seriesDecomposition, map_sum, rangeDecomposition] at expanded
  have zeroNotOne : (0 : Nat) ≠ 1 := by omega
  have zeroNotNonlinear : (0 : Nat) ∉ Finset.Icc 2 power := by simp
  have oneNotNonlinear : (1 : Nat) ∉ Finset.Icc 2 power := by simp
  rw [Finset.sum_insert (by simp [zeroNotOne, zeroNotNonlinear]),
    Finset.sum_insert oneNotNonlinear] at expanded
  have tailConstantZero : PowerSeries.constantCoeff tail = 0 := by
    simp [tail, constant]
  have constantCoeffAtOrder :
      PowerSeries.coeff order (PowerSeries.C constant) = 0 :=
    PowerSeries.coeff_C_of_ne_zero orderPositive.ne'
  have tailCoeff : PowerSeries.coeff order tail =
      PowerSeries.coeff order series := by
    rw [show tail = series - PowerSeries.C constant by rfl, map_sub,
      constantCoeffAtOrder, sub_zero]
  have coeffTerm (exponent : Nat) :
      PowerSeries.coeff order
          (tail ^ exponent * PowerSeries.C constant ^ (power - exponent) *
            (power.choose exponent : PowerSeries R)) =
        (power.choose exponent : R) * constant ^ (power - exponent) *
          PowerSeries.coeff order (tail ^ exponent) := by
    rw [mul_assoc]
    have constantProduct :
        PowerSeries.C constant ^ (power - exponent) *
            (power.choose exponent : PowerSeries R) =
          PowerSeries.C
            (constant ^ (power - exponent) * (power.choose exponent : R)) := by
      simp
    rw [constantProduct, PowerSeries.coeff_mul_C]
    ring
  rw [expanded]
  simp_rw [coeffTerm]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    pow_zero, one_mul, PowerSeries.coeff_one, orderPositive.ne', if_false,
    zero_mul, zero_add, pow_one]
  rw [tailCoeff]
  unfold nonlinearPowerCoefficient
  change _ = _ + ∑ nonlinearExponent ∈ Finset.Icc 2 power,
    (power.choose nonlinearExponent : R) *
      constant ^ (power - nonlinearExponent) *
        PowerSeries.coeff order (tail ^ nonlinearExponent)
  simp [constant]

/-- The preceding identity also covers exponent zero: at positive series
order both the linear contribution and the declared nonlinear sum vanish. -/
theorem coeff_pow_eq_linear_add_nonlinear_all
    {R : Type*} [CommRing R] (series : PowerSeries R)
    (power order : Nat) (orderPositive : 0 < order) :
    PowerSeries.coeff order (series ^ power) =
      (power : R) * PowerSeries.constantCoeff series ^ (power - 1) *
          PowerSeries.coeff order series +
        nonlinearPowerCoefficient power order series := by
  by_cases powerZero : power = 0
  · subst power
    simp [nonlinearPowerCoefficient, orderPositive.ne']
  · exact coeff_pow_eq_linear_add_nonlinear series power order
      (Nat.pos_of_ne_zero powerZero) orderPositive

/-- The part of the order-`t` evaluation coefficient left after removing
the unique occurrence of the order-`t` root coefficient.  Terms in the
second sum have positive `X`-series order; terms in the first have at least
two positive-order root coefficients. -/
noncomputable def nonlinearEvaluationCoefficient
    {R : Type*} [CommRing R]
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (order : Nat) : R :=
  ∑ exponent ∈ polynomial.support,
    (PowerSeries.constantCoeff (polynomial.coeff exponent) *
        nonlinearPowerCoefficient exponent order series +
      ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal order \ {(0, order)},
          PowerSeries.coeff pair.1 (polynomial.coeff exponent) *
            PowerSeries.coeff pair.2 (series ^ exponent))

/-- The same nonlinear coefficient, summed over an explicit fixed exponent
set.  This is essential under specialization: coefficients may become zero
and `Polynomial.support` may shrink, while the pre-specialization branch
index set must remain fixed. -/
noncomputable def nonlinearEvaluationCoefficientOn
    {R : Type*} [CommRing R] (indices : Finset Nat)
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (order : Nat) : R :=
  ∑ exponent ∈ indices,
    (PowerSeries.constantCoeff (polynomial.coeff exponent) *
        nonlinearPowerCoefficient exponent order series +
      ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal order \ {(0, order)},
        PowerSeries.coeff pair.1 (polynomial.coeff exponent) *
          PowerSeries.coeff pair.2 (series ^ exponent))

@[simp] theorem nonlinearEvaluationCoefficientOn_support
    {R : Type*} [CommRing R]
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (order : Nat) :
    nonlinearEvaluationCoefficientOn polynomial.support polynomial series order =
      nonlinearEvaluationCoefficient polynomial series order := by
  rfl

/-- Enlarging the fixed exponent set does not change the nonlinear
coefficient.  Exponents lost from support after specialization contribute
literal zero terms. -/
theorem nonlinearEvaluationCoefficientOn_eq
    {R : Type*} [CommRing R] (indices : Finset Nat)
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (order : Nat)
    (supportSubset : polynomial.support ⊆ indices) :
    nonlinearEvaluationCoefficientOn indices polynomial series order =
      nonlinearEvaluationCoefficient polynomial series order := by
  classical
  unfold nonlinearEvaluationCoefficientOn nonlinearEvaluationCoefficient
  symm
  apply Finset.sum_subset supportSubset
  intro exponent exponentMem exponentNotMem
  have coefficientZero : polynomial.coeff exponent = 0 := by
    simpa [Polynomial.mem_support_iff] using exponentNotMem
  simp [coefficientZero]

/-- Split one product coefficient into its coefficient-series constant term
and the terms of strictly positive coefficient-series order. -/
theorem coeff_mul_eq_constant_add_positive
    {R : Type*} [CommRing R]
    (coefficient series : PowerSeries R) (order : Nat) :
    PowerSeries.coeff order (coefficient * series) =
      PowerSeries.constantCoeff coefficient *
          PowerSeries.coeff order series +
        ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal order \ {(0, order)},
          PowerSeries.coeff pair.1 coefficient *
            PowerSeries.coeff pair.2 series := by
  classical
  rw [PowerSeries.coeff_mul]
  have split := Finset.sum_eq_add_sum_sdiff_singleton_of_mem
    (f := fun pair : Nat × Nat =>
      PowerSeries.coeff pair.1 coefficient *
        PowerSeries.coeff pair.2 series)
    (i := (0, order)) (by simp :
      (0, order) ∈ Finset.HasAntidiagonal.antidiagonal order)
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using split

/-- Exact characteristic-free implicit coefficient equation.  The first
term is the formal derivative evaluated at the constant root; every other
term is exposed by `nonlinearEvaluationCoefficient`. -/
theorem coeff_eval_eq_derivative_mul_add_nonlinear
    {R : Type*} [CommRing R]
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (order : Nat) (orderPositive : 0 < order) :
    PowerSeries.coeff order (polynomial.eval series) =
      PowerSeries.constantCoeff
          (polynomial.derivative.eval
            (PowerSeries.C (PowerSeries.constantCoeff series))) *
          PowerSeries.coeff order series +
        nonlinearEvaluationCoefficient polynomial series order := by
  classical
  rw [Polynomial.eval_eq_sum]
  change PowerSeries.coeff order
      (∑ exponent ∈ polynomial.support,
        polynomial.coeff exponent * series ^ exponent) = _
  rw [map_sum]
  simp_rw [coeff_mul_eq_constant_add_positive]
  simp_rw [coeff_pow_eq_linear_add_nonlinear_all series _ order
    orderPositive]
  have derivativeConstant :
      PowerSeries.constantCoeff
          (polynomial.derivative.eval
            (PowerSeries.C (PowerSeries.constantCoeff series))) =
        ∑ exponent ∈ polynomial.support,
          PowerSeries.constantCoeff (polynomial.coeff exponent) *
            (exponent : R) *
              PowerSeries.constantCoeff series ^ (exponent - 1) := by
    rw [Polynomial.derivative_eval]
    change PowerSeries.constantCoeff
        (∑ exponent ∈ polynomial.support,
          polynomial.coeff exponent * (exponent : PowerSeries R) *
            PowerSeries.C (PowerSeries.constantCoeff series) ^
              (exponent - 1)) = _
    rw [map_sum]
    simp only [map_mul, map_natCast, PowerSeries.constantCoeff_C, map_pow]
  rw [derivativeConstant]
  unfold nonlinearEvaluationCoefficient
  rw [Finset.sum_mul]
  simp only [mul_add, Finset.sum_add_distrib]
  have linearReorder :
      (∑ exponent ∈ polynomial.support,
        PowerSeries.constantCoeff (polynomial.coeff exponent) *
          ((exponent : R) *
            PowerSeries.constantCoeff series ^ (exponent - 1) *
              PowerSeries.coeff order series)) =
      ∑ exponent ∈ polynomial.support,
        PowerSeries.constantCoeff series ^ (exponent - 1) *
            PowerSeries.coeff order series *
              PowerSeries.constantCoeff (polynomial.coeff exponent) *
                (exponent : R) := by
    apply Finset.sum_congr rfl
    intro exponent _
    ring
  have linearReorderRight :
      (∑ exponent ∈ polynomial.support,
        PowerSeries.constantCoeff (polynomial.coeff exponent) *
            (exponent : R) *
              PowerSeries.constantCoeff series ^ (exponent - 1) *
                PowerSeries.coeff order series) =
      ∑ exponent ∈ polynomial.support,
        PowerSeries.constantCoeff series ^ (exponent - 1) *
            PowerSeries.coeff order series *
              PowerSeries.constantCoeff (polynomial.coeff exponent) *
                (exponent : R) := by
    apply Finset.sum_congr rfl
    intro exponent _
    ring
  rw [linearReorder, linearReorderRight]
  abel

/-- The exact recursive equation satisfied by a power-series root.  No
division is performed here: the derivative stays as a visible multiplier,
which is essential before passing to the regular quotient. -/
theorem derivative_mul_coeff_eq_neg_nonlinear_of_isRoot
    {R : Type*} [CommRing R]
    (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (root : polynomial.IsRoot series)
    (order : Nat) (orderPositive : 0 < order) :
    PowerSeries.constantCoeff
          (polynomial.derivative.eval
            (PowerSeries.C (PowerSeries.constantCoeff series))) *
        PowerSeries.coeff order series =
      -nonlinearEvaluationCoefficient polynomial series order := by
  have coefficientZero := congrArg (PowerSeries.coeff order) root.eq_zero
  rw [coeff_eval_eq_derivative_mul_add_nonlinear polynomial series order
    orderPositive] at coefficientZero
  simp at coefficientZero
  exact eq_neg_of_add_eq_zero_left coefficientZero

/-- Fixed-index form of the characteristic-free root recurrence. -/
theorem derivative_mul_coeff_eq_neg_nonlinearOn_of_isRoot
    {R : Type*} [CommRing R]
    (indices : Finset Nat) (polynomial : Polynomial (PowerSeries R))
    (series : PowerSeries R) (root : polynomial.IsRoot series)
    (order : Nat) (orderPositive : 0 < order)
    (supportSubset : polynomial.support ⊆ indices) :
    PowerSeries.constantCoeff
          (polynomial.derivative.eval
            (PowerSeries.C (PowerSeries.constantCoeff series))) *
        PowerSeries.coeff order series =
      -nonlinearEvaluationCoefficientOn indices polynomial series order := by
  rw [nonlinearEvaluationCoefficientOn_eq indices polynomial series order
    supportSubset]
  exact derivative_mul_coeff_eq_neg_nonlinear_of_isRoot polynomial series root
    order orderPositive

#print axioms sum_henselDenominatorExponent_add_positivePartCount
#print axioms sum_henselDenominatorExponent_le_two_mul_sub_one
#print axioms sum_henselDenominatorExponent_le_two_mul_sub_two
#print axioms sum_henselDenominatorExponent_le_two_mul
#print axioms sum_henselDenominatorExponent_le_target_sub_one_of_total_lt
#print axioms clear_hensel_product_denominators
#print axioms exists_unique_full_part_of_positivePartCount_eq_one
#print axioms positivePartCount_range_eq_of_coeffProduct_ne_zero
#print axioms convolution_henselExponent_le_two_mul_sub_two
#print axioms coeff_pow_eq_linear_add_nonlinear
#print axioms coeff_pow_eq_linear_add_nonlinear_all
#print axioms coeff_mul_eq_constant_add_positive
#print axioms coeff_eval_eq_derivative_mul_add_nonlinear
#print axioms derivative_mul_coeff_eq_neg_nonlinear_of_isRoot
#print axioms nonlinearEvaluationCoefficientOn_eq
#print axioms derivative_mul_coeff_eq_neg_nonlinearOn_of_isRoot

end AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics
