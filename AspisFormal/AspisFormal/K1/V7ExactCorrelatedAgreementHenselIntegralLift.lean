import AspisFormal.K1.V7ExactCorrelatedAgreementHenselWeights

/-!
# Integral positive-order Hensel coefficients

This module constructs the literal regular-ring representative of the
nonlinear side of the characteristic-free Hensel recurrence.  The two kinds
of summands are kept separate:

* zero shifted-`X` order and at least two positive root coefficients;
* positive shifted-`X` order, hence strictly smaller root-series order.

That distinction is what provides the one saved `eta` power needed to solve
the recurrence without division in the regular ring.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementHenselIntegralLift

open scoped BigOperators
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementHenselCombinatorics
open AspisK1.V7ExactCorrelatedAgreementHenselWeights
open AspisK1.V7ExactCorrelatedAgreementPowerSeriesLift
open AspisK1.V7ExactCorrelatedAgreementHenselRecurrence
open AspisK1.V7ExactCorrelatedAgreementFunctionField
open AspisK1.V7ExactCorrelatedAgreementRegularRing
open AspisK1.V7ExactCorrelatedAgreementRegularHensel
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Replace the constant coefficient by zero while retaining every positive
coefficient's already-cleared representative. -/
def clearedTail {O : Type*} [Zero O] (cleared : Nat → O) (order : Nat) : O :=
  if order = 0 then 0 else cleared order

theorem map_clearedTail
    {O F : Type*} [CommRing O] [CommRing F]
    (mapToField : O →+* F) (leading eta : O) (cleared : Nat → O)
    (series : PowerSeries F)
    (clearedImage : ∀ coefficientOrder,
      mapToField (cleared coefficientOrder) =
        mapToField leading *
          mapToField eta ^ henselDenominatorExponent coefficientOrder *
            PowerSeries.coeff coefficientOrder series)
    (order : Nat) :
    mapToField (clearedTail cleared order) =
      mapToField leading *
        mapToField eta ^ henselDenominatorExponent order *
          PowerSeries.coeff order
            (series - PowerSeries.C (PowerSeries.constantCoeff series)) := by
  by_cases orderZero : order = 0
  · subst order
    simp [clearedTail]
  · rw [clearedTail, if_neg orderZero, clearedImage]
    rw [map_sub, PowerSeries.coeff_C_of_ne_zero orderZero, sub_zero]

/-- Integral representative of the nonlinear side over one fixed exponent
set, already multiplied by `leading^degree * eta^(e_t-1)`.  Keeping this set
explicit prevents specialization-induced support shrinkage from changing the
chosen global recurrence. -/
noncomputable def regularClearedNonlinearEvaluationCoefficientOn
    {O F : Type*} [CommRing O] [CommRing F] [DecidableEq F]
    (indices : Finset Nat)
    (coefficientRepresentative : Nat → Nat → O)
    (series : PowerSeries F) (leading eta : O) (cleared : Nat → O)
    (degree order : Nat) : O :=
  ∑ exponent ∈ indices,
    ((∑ nonlinearExponent ∈ Finset.Icc 2 exponent,
          coefficientRepresentative exponent 0 *
          (exponent.choose nonlinearExponent : O) *
            leading ^ (degree - exponent) *
              cleared 0 ^ (exponent - nonlinearExponent) *
                regularClearedSupportedPowerCoefficient leading eta
                  (clearedTail cleared)
                  (series - PowerSeries.C
                    (PowerSeries.constantCoeff series))
                  nonlinearExponent order
                  (henselDenominatorExponent order - 1)) +
      ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal order \ {(0, order)},
        coefficientRepresentative exponent pair.1 *
          leading ^ (degree - exponent) *
            regularClearedPowerCoefficient leading eta cleared
              exponent pair.2 (henselDenominatorExponent order - 1))

/-- Source-support wrapper used by the fixed algebraic branch. -/
noncomputable def regularClearedNonlinearEvaluationCoefficient
    {O F : Type*} [CommRing O] [CommRing F] [DecidableEq F]
    (polynomial : Polynomial (PowerSeries F))
    (coefficientRepresentative : Nat → Nat → O)
    (series : PowerSeries F) (leading eta : O) (cleared : Nat → O)
    (degree order : Nat) : O :=
  regularClearedNonlinearEvaluationCoefficientOn polynomial.support
    coefficientRepresentative series leading eta cleared degree order

private theorem tail_constantCoeff_zero
    {F : Type*} [CommRing F] (series : PowerSeries F) :
    PowerSeries.constantCoeff
        (series - PowerSeries.C (PowerSeries.constantCoeff series)) = 0 := by
  simp

private theorem nonlinear_supported_exponentBound
    {F : Type*} [CommRing F] [DecidableEq F]
    (series : PowerSeries F) (power order : Nat) (powerAtLeastTwo : 2 ≤ power)
    (parts : Nat →₀ Nat)
    (partsMem : parts ∈
      ((Finset.range power).finsuppAntidiag order).filter
        (fun tuple : Nat →₀ Nat => ∏ index ∈ Finset.range power,
          PowerSeries.coeff (tuple index)
            (series - PowerSeries.C (PowerSeries.constantCoeff series)) ≠ 0)) :
    ∑ index ∈ Finset.range power,
        henselDenominatorExponent (parts index) ≤
      henselDenominatorExponent order - 1 := by
  have antidiagonalMem := (Finset.mem_filter.mp partsMem).1
  have productNeZero := (Finset.mem_filter.mp partsMem).2
  have bounded := convolution_henselExponent_le_two_mul_sub_two
    (series - PowerSeries.C (PowerSeries.constantCoeff series))
    (tail_constantCoeff_zero series) power order powerAtLeastTwo parts
      antidiagonalMem productNeZero
  by_cases orderZero : order = 0
  · subst order
    have partsZero : parts = 0 := by simpa using antidiagonalMem
    subst parts
    have zeroMem : 0 ∈ Finset.range power := by
      exact Finset.mem_range.mpr (lt_of_lt_of_le (by omega) powerAtLeastTwo)
    have productZero :
        ∏ index ∈ Finset.range power,
          PowerSeries.coeff ((0 : Nat →₀ Nat) index)
            (series - PowerSeries.C (PowerSeries.constantCoeff series)) = 0 := by
      apply Finset.prod_eq_zero zeroMem
      simp [tail_constantCoeff_zero]
    exact (productNeZero productZero).elim
  · have exponentIdentity : henselDenominatorExponent order - 1 =
        2 * order - 2 := by
      unfold henselDenominatorExponent
      omega
    rwa [exponentIdentity]

private theorem nonlinear_supported_part_lt_order
    {F : Type*} [CommRing F] [DecidableEq F]
    (series : PowerSeries F) (power order : Nat) (powerAtLeastTwo : 2 ≤ power)
    (parts : Nat →₀ Nat)
    (partsMem : parts ∈
      ((Finset.range power).finsuppAntidiag order).filter
        (fun tuple : Nat →₀ Nat => ∏ index ∈ Finset.range power,
          PowerSeries.coeff (tuple index)
            (series - PowerSeries.C (PowerSeries.constantCoeff series)) ≠ 0))
    (index : Nat) (indexMem : index ∈ Finset.range power) :
    parts index < order := by
  let tail := series - PowerSeries.C (PowerSeries.constantCoeff series)
  have antidiagonalMem := (Finset.mem_filter.mp partsMem).1
  have productNeZero := (Finset.mem_filter.mp partsMem).2
  have partsSum : ∑ other ∈ Finset.range power, parts other = order :=
    (Finset.mem_finsuppAntidiag.mp antidiagonalMem).1
  have allPositive : ∀ other ∈ Finset.range power, 0 < parts other := by
    intro other otherMem
    have coefficientNeZero : PowerSeries.coeff (parts other) tail ≠ 0 := by
      intro coefficientZero
      exact productNeZero (Finset.prod_eq_zero otherMem coefficientZero)
    by_contra notPositive
    have partZero : parts other = 0 := by omega
    rw [partZero, PowerSeries.coeff_zero_eq_constantCoeff,
      show PowerSeries.constantCoeff tail = 0 by simp [tail]] at coefficientNeZero
    exact coefficientNeZero rfl
  have rangeNontrivial : (Finset.range power).Nontrivial := by
    rw [← Finset.one_lt_card_iff_nontrivial, Finset.card_range]
    omega
  obtain ⟨other, otherMem, otherNe⟩ := rangeNontrivial.exists_ne index
  have strict := Finset.single_lt_sum (s := Finset.range power)
    otherNe indexMem otherMem (allPositive other otherMem)
      (fun candidate _ _ => Nat.zero_le (parts candidate))
  rwa [partsSum] at strict

private theorem positive_shift_exponentBound
    (power order : Nat) (pair : Nat × Nat)
    (pairMem : pair ∈
      Finset.HasAntidiagonal.antidiagonal order \ {(0, order)})
    (parts : Nat →₀ Nat)
    (partsMem : parts ∈ (Finset.range power).finsuppAntidiag pair.2) :
    ∑ index ∈ Finset.range power,
        henselDenominatorExponent (parts index) ≤
      henselDenominatorExponent order - 1 := by
  have pairSum : pair.1 + pair.2 = order := by
    exact Finset.HasAntidiagonal.mem_antidiagonal.mp
      (Finset.mem_sdiff.mp pairMem).1
  have pairNe : pair ≠ (0, order) := by
    simpa using (Finset.mem_sdiff.mp pairMem).2
  have secondLt : pair.2 < order := by
    by_contra notLt
    have secondEq : pair.2 = order := by omega
    have firstZero : pair.1 = 0 := by omega
    exact pairNe (Prod.ext firstZero secondEq)
  have partsSum : ∑ index ∈ Finset.range power, parts index = pair.2 :=
    (Finset.mem_finsuppAntidiag.mp partsMem).1
  exact sum_henselDenominatorExponent_le_target_sub_one_of_total_lt
    (Finset.range power) parts pair.2 order partsSum secondLt

private theorem leading_clearedConstant_supportedPower
    {R : Type*} [CommRing R]
    (leading constant nonlinearValue : R)
    (degree exponent nonlinearExponent : Nat)
    (exponentLe : exponent ≤ degree)
    (nonlinearLe : nonlinearExponent ≤ exponent) :
    leading ^ (degree - exponent) *
        (leading * constant) ^ (exponent - nonlinearExponent) *
          (leading ^ nonlinearExponent * nonlinearValue) =
      leading ^ degree *
        constant ^ (exponent - nonlinearExponent) * nonlinearValue := by
  rw [mul_pow]
  have nonlinearSplit :
      exponent - nonlinearExponent + nonlinearExponent = exponent :=
    Nat.sub_add_cancel nonlinearLe
  have degreeSplit : degree - exponent + exponent = degree :=
    Nat.sub_add_cancel exponentLe
  calc
    leading ^ (degree - exponent) *
          (leading ^ (exponent - nonlinearExponent) *
            constant ^ (exponent - nonlinearExponent)) *
          (leading ^ nonlinearExponent * nonlinearValue) =
        (leading ^ (degree - exponent) *
          (leading ^ (exponent - nonlinearExponent) *
            leading ^ nonlinearExponent)) *
          constant ^ (exponent - nonlinearExponent) * nonlinearValue := by
      ac_rfl
    _ = leading ^ degree *
          constant ^ (exponent - nonlinearExponent) * nonlinearValue := by
      rw [← pow_add, nonlinearSplit, ← pow_add, degreeSplit]

private theorem leading_residual_mul_power
    {R : Type*} [CommRing R] (leading value : R)
    (degree exponent : Nat) (exponentLe : exponent ≤ degree) :
    leading ^ (degree - exponent) * (leading ^ exponent * value) =
      leading ^ degree * value := by
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel exponentLe]

/-- Exact image identity for the regular nonlinear recurrence
representative. -/
theorem map_regularClearedNonlinearEvaluationCoefficientOn
    {O F S : Type*} [CommRing O] [CommRing F] [CommRing S] [IsDomain S]
    [DecidableEq S]
    (mapToField : O →+* F)
    (indices : Finset Nat)
    (polynomial : Polynomial (PowerSeries F))
    (coefficientRepresentative : Nat → Nat → O)
    (supportSeries : PowerSeries S) (series : PowerSeries F)
    (leading eta : O) (cleared : Nat → O)
    (degree order : Nat)
    (orderPositive : 0 < order)
    (indexDegree : ∀ exponent ∈ indices, exponent ≤ degree)
    (coefficientImage : ∀ exponent coefficientOrder,
      mapToField (coefficientRepresentative exponent coefficientOrder) =
        PowerSeries.coeff coefficientOrder (polynomial.coeff exponent))
    (clearedImage : ∀ coefficientOrder < order,
      mapToField (cleared coefficientOrder) =
        mapToField leading *
          mapToField eta ^ henselDenominatorExponent coefficientOrder *
            PowerSeries.coeff coefficientOrder series)
    (supportOfTarget : ∀ coefficientOrder < order,
      PowerSeries.coeff coefficientOrder series ≠ 0 →
        PowerSeries.coeff coefficientOrder supportSeries ≠ 0) :
    mapToField (regularClearedNonlinearEvaluationCoefficientOn indices
        coefficientRepresentative supportSeries leading eta cleared degree order) =
      mapToField leading ^ degree *
        mapToField eta ^ (henselDenominatorExponent order - 1) *
          nonlinearEvaluationCoefficientOn indices polynomial series order := by
  classical
  unfold regularClearedNonlinearEvaluationCoefficientOn
  unfold nonlinearEvaluationCoefficientOn
  rw [map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro exponent exponentMem
  have exponentLe : exponent ≤ degree := indexDegree exponent exponentMem
  rw [map_add, map_sum, map_sum, mul_add]
  congr 1
  · unfold nonlinearPowerCoefficient
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro nonlinearExponent nonlinearMem
    have nonlinearLe : nonlinearExponent ≤ exponent :=
      (Finset.mem_Icc.mp nonlinearMem).2
    simp only [map_mul, map_natCast, map_pow, coefficientImage]
    rw [map_regularClearedSupportedPowerCoefficient_of_specialization
      mapToField leading eta
      (clearedTail cleared)
      (supportSeries - PowerSeries.C
        (PowerSeries.constantCoeff supportSeries))
      (series - PowerSeries.C (PowerSeries.constantCoeff series))
      nonlinearExponent order (henselDenominatorExponent order - 1)
      (by
        intro parts partsMem index indexMem
        let tail := series - PowerSeries.C
          (PowerSeries.constantCoeff series)
        by_cases partZero : parts index = 0
        · rw [partZero]
          simp [clearedTail, tail]
        · rw [clearedTail, if_neg partZero]
          rw [clearedImage (parts index)
            (nonlinear_supported_part_lt_order supportSeries nonlinearExponent order
              (Finset.mem_Icc.mp nonlinearMem).1 parts partsMem index indexMem)]
          rw [map_sub, PowerSeries.coeff_C_of_ne_zero partZero, sub_zero])
      (by
        intro parts partsMem targetProductNeZero
        apply Finset.prod_ne_zero_iff.mpr
        intro index indexMem
        have targetCoefficientNeZero : PowerSeries.coeff (parts index)
            (series - PowerSeries.C (PowerSeries.constantCoeff series)) ≠ 0 := by
          intro coefficientZero
          exact targetProductNeZero
            (Finset.prod_eq_zero indexMem coefficientZero)
        have partPositive : 0 < parts index := by
          by_contra notPositive
          have partZero : parts index = 0 := by omega
          rw [partZero, PowerSeries.coeff_zero_eq_constantCoeff] at targetCoefficientNeZero
          exact targetCoefficientNeZero (by simp)
        rw [map_sub, PowerSeries.coeff_C_of_ne_zero partPositive.ne', sub_zero]
        exact supportOfTarget (parts index)
          (nonlinear_supported_part_lt_order series nonlinearExponent order
            (Finset.mem_Icc.mp nonlinearMem).1 parts
            (Finset.mem_filter.mpr ⟨
              partsMem,
              targetProductNeZero⟩) index indexMem)
          (by
            rw [map_sub, PowerSeries.coeff_C_of_ne_zero partPositive.ne',
              sub_zero] at targetCoefficientNeZero
            exact targetCoefficientNeZero))]
    · rw [clearedImage 0 orderPositive, henselDenominatorExponent_zero,
        pow_zero, mul_one,
        PowerSeries.coeff_zero_eq_constantCoeff]
      have leadingIdentity := leading_clearedConstant_supportedPower
        (mapToField leading) (PowerSeries.constantCoeff series)
        (mapToField eta ^ (henselDenominatorExponent order - 1) *
          PowerSeries.coeff order
            ((series - PowerSeries.C
              (PowerSeries.constantCoeff series)) ^ nonlinearExponent))
        degree exponent nonlinearExponent exponentLe nonlinearLe
      calc
        PowerSeries.constantCoeff (polynomial.coeff exponent) *
            (exponent.choose nonlinearExponent : F) *
            mapToField leading ^ (degree - exponent) *
            (mapToField leading * PowerSeries.constantCoeff series) ^
              (exponent - nonlinearExponent) *
            (mapToField leading ^ nonlinearExponent *
              mapToField eta ^ (henselDenominatorExponent order - 1) *
              PowerSeries.coeff order
                ((series - PowerSeries.C
                  (PowerSeries.constantCoeff series)) ^
                    nonlinearExponent)) =
          PowerSeries.constantCoeff (polynomial.coeff exponent) *
            (exponent.choose nonlinearExponent : F) *
              (mapToField leading ^ (degree - exponent) *
                (mapToField leading * PowerSeries.constantCoeff series) ^
                  (exponent - nonlinearExponent) *
                (mapToField leading ^ nonlinearExponent *
                  (mapToField eta ^
                    (henselDenominatorExponent order - 1) *
                    PowerSeries.coeff order
                      ((series - PowerSeries.C
                        (PowerSeries.constantCoeff series)) ^
                          nonlinearExponent)))) := by ring
        _ = PowerSeries.constantCoeff (polynomial.coeff exponent) *
            (exponent.choose nonlinearExponent : F) *
              (mapToField leading ^ degree *
                PowerSeries.constantCoeff series ^
                  (exponent - nonlinearExponent) *
                (mapToField eta ^
                  (henselDenominatorExponent order - 1) *
                  PowerSeries.coeff order
                    ((series - PowerSeries.C
                      (PowerSeries.constantCoeff series)) ^
                        nonlinearExponent))) := by rw [leadingIdentity]
        _ = _ := by ring
    · intro parts partsMem
      exact nonlinear_supported_exponentBound supportSeries nonlinearExponent order
        (Finset.mem_Icc.mp nonlinearMem).1 parts partsMem
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pair pairMem
    simp only [map_mul, map_pow]
    rw [map_regularClearedPowerCoefficient mapToField leading eta cleared
      series exponent pair.2 (henselDenominatorExponent order - 1)
      (by
        intro parts partsMem index indexMem
        have partsSum : ∑ other ∈ Finset.range exponent, parts other =
            pair.2 := (Finset.mem_finsuppAntidiag.mp partsMem).1
        have partLe : parts index ≤ pair.2 := by
          rw [← partsSum]
          exact Finset.single_le_sum
            (fun candidate _ => Nat.zero_le (parts candidate)) indexMem
        have pairSum : pair.1 + pair.2 = order :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp
            (Finset.mem_sdiff.mp pairMem).1
        have pairNe : pair ≠ (0, order) := by
          simpa using (Finset.mem_sdiff.mp pairMem).2
        have secondLt : pair.2 < order := by
          by_contra notLt
          have secondEq : pair.2 = order := by omega
          have firstZero : pair.1 = 0 := by omega
          exact pairNe (Prod.ext firstZero secondEq)
        exact clearedImage (parts index) (partLe.trans_lt secondLt))]
    · rw [coefficientImage]
      have leadingIdentity := leading_residual_mul_power (mapToField leading)
        (mapToField eta ^ (henselDenominatorExponent order - 1) *
          PowerSeries.coeff pair.2 (series ^ exponent))
        degree exponent exponentLe
      calc
        PowerSeries.coeff pair.1 (polynomial.coeff exponent) *
            mapToField leading ^ (degree - exponent) *
            (mapToField leading ^ exponent *
              mapToField eta ^ (henselDenominatorExponent order - 1) *
              PowerSeries.coeff pair.2 (series ^ exponent)) =
          PowerSeries.coeff pair.1 (polynomial.coeff exponent) *
            (mapToField leading ^ (degree - exponent) *
              (mapToField leading ^ exponent *
                (mapToField eta ^ (henselDenominatorExponent order - 1) *
                  PowerSeries.coeff pair.2 (series ^ exponent)))) := by ring
        _ = PowerSeries.coeff pair.1 (polynomial.coeff exponent) *
            (mapToField leading ^ degree *
              (mapToField eta ^ (henselDenominatorExponent order - 1) *
                PowerSeries.coeff pair.2 (series ^ exponent))) := by
          rw [leadingIdentity]
        _ = _ := by ring
    · intro parts partsMem
      exact positive_shift_exponentBound exponent order pair pairMem parts
        partsMem

/-- Source-support form of the preceding fixed-index commuting theorem. -/
theorem map_regularClearedNonlinearEvaluationCoefficient
    {O F : Type*} [CommRing O] [CommRing F] [IsDomain F] [DecidableEq F]
    (mapToField : O →+* F)
    (polynomial : Polynomial (PowerSeries F))
    (coefficientRepresentative : Nat → Nat → O)
    (series : PowerSeries F) (leading eta : O) (cleared : Nat → O)
    (degree order : Nat)
    (orderPositive : 0 < order)
    (polynomialDegree : polynomial.natDegree ≤ degree)
    (coefficientImage : ∀ exponent coefficientOrder,
      mapToField (coefficientRepresentative exponent coefficientOrder) =
        PowerSeries.coeff coefficientOrder (polynomial.coeff exponent))
    (clearedImage : ∀ coefficientOrder < order,
      mapToField (cleared coefficientOrder) =
        mapToField leading *
          mapToField eta ^ henselDenominatorExponent coefficientOrder *
            PowerSeries.coeff coefficientOrder series) :
    mapToField (regularClearedNonlinearEvaluationCoefficient polynomial
        coefficientRepresentative series leading eta cleared degree order) =
      mapToField leading ^ degree *
        mapToField eta ^ (henselDenominatorExponent order - 1) *
          nonlinearEvaluationCoefficient polynomial series order := by
  simpa only [regularClearedNonlinearEvaluationCoefficient,
    nonlinearEvaluationCoefficientOn_support] using
    map_regularClearedNonlinearEvaluationCoefficientOn mapToField
      polynomial.support polynomial coefficientRepresentative series series leading
      eta cleared degree order orderPositive
      (fun exponent exponentMem =>
        (Polynomial.le_natDegree_of_mem_supp exponent exponentMem).trans
          polynomialDegree)
      coefficientImage clearedImage (fun _ _ nonzero => nonzero)

/-- One denominator-free Hensel step commutes with an arbitrary ring
specialization.  The hypotheses expose the two facts that matter at the
specialized point: the shifted polynomial coefficients have the stated
regular representatives, and `eta` is the explicitly cleared derivative.
No division, separability convention, or characteristic-zero derivative
identity is hidden in this lemma. -/
theorem map_neg_regularClearedNonlinearEvaluationCoefficientOn_of_isRoot
    {O F S : Type*} [CommRing O] [CommRing F] [CommRing S] [IsDomain S]
    [DecidableEq S]
    (mapToField : O →+* F)
    (indices : Finset Nat)
    (polynomial : Polynomial (PowerSeries F))
    (coefficientRepresentative : Nat → Nat → O)
    (supportSeries : PowerSeries S) (series : PowerSeries F)
    (leading eta : O) (cleared : Nat → O)
    (degree order : Nat)
    (degreePositive : 0 < degree) (orderPositive : 0 < order)
    (indexDegree : ∀ exponent ∈ indices, exponent ≤ degree)
    (supportSubset : polynomial.support ⊆ indices)
    (coefficientImage : ∀ exponent coefficientOrder,
      mapToField (coefficientRepresentative exponent coefficientOrder) =
        PowerSeries.coeff coefficientOrder (polynomial.coeff exponent))
    (clearedImage : ∀ coefficientOrder < order,
      mapToField (cleared coefficientOrder) =
        mapToField leading *
          mapToField eta ^ henselDenominatorExponent coefficientOrder *
            PowerSeries.coeff coefficientOrder series)
    (supportOfTarget : ∀ coefficientOrder < order,
      PowerSeries.coeff coefficientOrder series ≠ 0 →
        PowerSeries.coeff coefficientOrder supportSeries ≠ 0)
    (rootEquation : polynomial.IsRoot series)
    (etaImage : mapToField eta =
      mapToField leading ^ (degree - 1) *
        PowerSeries.constantCoeff
          (polynomial.derivative.eval
            (PowerSeries.C (PowerSeries.constantCoeff series)))) :
    mapToField (-regularClearedNonlinearEvaluationCoefficientOn indices
        coefficientRepresentative supportSeries leading eta cleared degree order) =
      mapToField leading *
        mapToField eta ^ henselDenominatorExponent order *
          PowerSeries.coeff order series := by
  have nonlinearImage := map_regularClearedNonlinearEvaluationCoefficientOn
    mapToField indices polynomial coefficientRepresentative supportSeries series
      leading eta cleared degree order orderPositive indexDegree coefficientImage
      clearedImage supportOfTarget
  have recurrence := derivative_mul_coeff_eq_neg_nonlinearOn_of_isRoot
    indices polynomial series rootEquation order orderPositive supportSubset
  have degreeSplit : degree - 1 + 1 = degree :=
    Nat.sub_add_cancel degreePositive
  have exponentSplit : henselDenominatorExponent order - 1 + 1 =
      henselDenominatorExponent order := by
    unfold henselDenominatorExponent
    omega
  rw [map_neg, nonlinearImage]
  have etaPower :
      mapToField eta ^ henselDenominatorExponent order =
        mapToField eta ^ (henselDenominatorExponent order - 1) *
          mapToField eta := by
    calc
      mapToField eta ^ henselDenominatorExponent order =
          mapToField eta ^
            (henselDenominatorExponent order - 1 + 1) := by
        rw [exponentSplit]
      _ = _ := pow_succ _ _
  calc
    -(mapToField leading ^ degree *
          mapToField eta ^ (henselDenominatorExponent order - 1) *
            nonlinearEvaluationCoefficientOn indices polynomial series order) =
        mapToField leading ^ degree *
          mapToField eta ^ (henselDenominatorExponent order - 1) *
            (PowerSeries.constantCoeff
                (polynomial.derivative.eval
                  (PowerSeries.C (PowerSeries.constantCoeff series))) *
              PowerSeries.coeff order series) := by
      rw [recurrence]
      ring
    _ = mapToField leading *
          (mapToField eta ^ (henselDenominatorExponent order - 1) *
            (mapToField leading ^ (degree - 1) *
              PowerSeries.constantCoeff
                (polynomial.derivative.eval
                  (PowerSeries.C (PowerSeries.constantCoeff series))))) *
          PowerSeries.coeff order series := by
      rw [show mapToField leading ^ degree =
          mapToField leading ^ (degree - 1) * mapToField leading by
        rw [← pow_succ, degreeSplit]]
      ring
    _ = mapToField leading *
          mapToField eta ^ henselDenominatorExponent order *
            PowerSeries.coeff order series := by
      rw [etaPower, etaImage]

/-- Source-support wrapper for the fixed algebraic branch. -/
theorem map_neg_regularClearedNonlinearEvaluationCoefficient_of_isRoot
    {O F : Type*} [CommRing O] [CommRing F] [IsDomain F] [DecidableEq F]
    (mapToField : O →+* F)
    (polynomial : Polynomial (PowerSeries F))
    (coefficientRepresentative : Nat → Nat → O)
    (series : PowerSeries F) (leading eta : O) (cleared : Nat → O)
    (degree order : Nat)
    (degreePositive : 0 < degree) (orderPositive : 0 < order)
    (polynomialDegree : polynomial.natDegree ≤ degree)
    (coefficientImage : ∀ exponent coefficientOrder,
      mapToField (coefficientRepresentative exponent coefficientOrder) =
        PowerSeries.coeff coefficientOrder (polynomial.coeff exponent))
    (clearedImage : ∀ coefficientOrder < order,
      mapToField (cleared coefficientOrder) =
        mapToField leading *
          mapToField eta ^ henselDenominatorExponent coefficientOrder *
            PowerSeries.coeff coefficientOrder series)
    (rootEquation : polynomial.IsRoot series)
    (etaImage : mapToField eta =
      mapToField leading ^ (degree - 1) *
        PowerSeries.constantCoeff
          (polynomial.derivative.eval
            (PowerSeries.C (PowerSeries.constantCoeff series)))) :
    mapToField (-regularClearedNonlinearEvaluationCoefficient polynomial
        coefficientRepresentative series leading eta cleared degree order) =
      mapToField leading *
        mapToField eta ^ henselDenominatorExponent order *
          PowerSeries.coeff order series := by
  simpa only [regularClearedNonlinearEvaluationCoefficient] using
    map_neg_regularClearedNonlinearEvaluationCoefficientOn_of_isRoot
      mapToField polynomial.support polynomial coefficientRepresentative series
      series leading eta cleared degree order degreePositive orderPositive
      (fun exponent exponentMem =>
        (Polynomial.le_natDegree_of_mem_supp exponent exponentMem).trans
          polynomialDegree)
      (fun _ member => member) coefficientImage clearedImage
      (fun _ _ nonzero => nonzero) rootEquation etaImage

/-! ## Weight of the nonlinear representative -/

private theorem integralBranchIteratedWeight_natCast
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (value : Nat) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (value : IntegralLocalBranch localFactor) = 0 := by
  apply Nat.eq_zero_of_le_zero
  change integralBranchIteratedWeight localFactor localFactorNeZero
      (localBound + ell - ell * localFactor.natDegree)
      (AdjoinRoot.of (integralLocalFactor localFactor)
        (C (value : K))) ≤ 0
  exact (integralBranchIteratedWeight_of_le_natDegree localFactor
    localFactorNeZero ell localBound localCoefficientBound
      (C (value : K))).trans (by simp)

private theorem integralBranchIteratedWeight_mul_five_le
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (a b c d e : IntegralLocalBranch localFactor) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (a * b * c * d * e) ≤
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) a +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) b +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) c +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) d +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) e := by
  calc
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (a * b * c * d * e) ≤
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) (a * b * c * d) +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) e :=
      integralBranchIteratedWeight_mul_le localFactor localFactorNeZero ell
        localBound localCoefficientBound _ _
    _ ≤ (integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) (a * b * c) +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) d) +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) e := by
      gcongr
      exact integralBranchIteratedWeight_mul_le localFactor localFactorNeZero
        ell localBound localCoefficientBound _ _
    _ ≤ ((integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) (a * b) +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) c) +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) d) +
        integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) e := by
      gcongr
      exact integralBranchIteratedWeight_mul_le localFactor localFactorNeZero
        ell localBound localCoefficientBound _ _
    _ ≤ _ := by
      gcongr
      exact integralBranchIteratedWeight_mul_le localFactor localFactorNeZero
        ell localBound localCoefficientBound _ _

/-- Generic weight estimate for the already-constructed nonlinear recurrence
representative.  `structuralBudget` isolates the one branch-specific weighted-
degree calculation; all convolution and denominator accounting is proved
here. -/
theorem regularClearedNonlinearEvaluationCoefficientOn_weight_le
    {K F : Type*} [Field K] [CommRing F] [DecidableEq F]
    (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound etaWeight : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (indices : Finset Nat)
    (coefficientRepresentative : Nat → Nat → IntegralLocalBranch localFactor)
    (coefficientDegree : Nat → Nat)
    (series : PowerSeries F)
    (leading eta : IntegralLocalBranch localFactor)
    (cleared : Nat → IntegralLocalBranch localFactor)
    (degree order leadingWeight : Nat)
    (orderPositive : 0 < order)
    (leadingWeightBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) leading ≤
        leadingWeight)
    (etaWeightBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) eta ≤ etaWeight)
    (coefficientWeight : ∀ exponent ∈ indices, ∀ coefficientOrder,
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree)
          (coefficientRepresentative exponent coefficientOrder) ≤
        coefficientDegree exponent)
    (structuralBudget : ∀ exponent ∈ indices,
      coefficientDegree exponent + (degree - exponent) * leadingWeight +
          exponent * (localBound + ell - ell * localFactor.natDegree) ≤
        (localBound + ell - ell * localFactor.natDegree) + etaWeight)
    (clearedWeight : ∀ coefficientOrder < order,
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree)
          (cleared coefficientOrder) ≤
        (localBound + ell - ell * localFactor.natDegree) +
          henselDenominatorExponent coefficientOrder * etaWeight) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (regularClearedNonlinearEvaluationCoefficientOn indices
          coefficientRepresentative series leading eta cleared degree order) ≤
      (localBound + ell - ell * localFactor.natDegree) +
        henselDenominatorExponent order * etaWeight := by
  classical
  let generatorWeight := localBound + ell - ell * localFactor.natDegree
  let target := generatorWeight + henselDenominatorExponent order * etaWeight
  have exponentSplit : henselDenominatorExponent order - 1 + 1 =
      henselDenominatorExponent order := by
    unfold henselDenominatorExponent
    omega
  unfold regularClearedNonlinearEvaluationCoefficientOn
  apply integralBranchIteratedWeight_finset_sum_le localFactor
    localFactorNeZero generatorWeight target
  intro exponent exponentMem
  apply (integralBranchIteratedWeight_add_le localFactor localFactorNeZero
    generatorWeight _ _).trans
  apply max_le
  · apply integralBranchIteratedWeight_finset_sum_le localFactor
      localFactorNeZero generatorWeight target
    intro nonlinearExponent nonlinearMem
    have nonlinearLe : nonlinearExponent ≤ exponent :=
      (Finset.mem_Icc.mp nonlinearMem).2
    have coefficientBound := coefficientWeight exponent exponentMem 0
    have leadingPowerBound :=
      (integralBranchIteratedWeight_pow_le localFactor localFactorNeZero ell
        localBound localCoefficientBound leading
          (degree - exponent)).trans
        (Nat.mul_le_mul_left _ leadingWeightBound)
    have constantPowerBound :=
      (integralBranchIteratedWeight_pow_le localFactor localFactorNeZero ell
        localBound localCoefficientBound (cleared 0)
          (exponent - nonlinearExponent)).trans
        (Nat.mul_le_mul_left _ <| by
          simpa [generatorWeight] using clearedWeight 0 orderPositive)
    have supportedPowerBound :=
      regularClearedSupportedPowerCoefficient_weight_le localFactor
        localFactorNeZero ell localBound etaWeight localCoefficientBound
        leading eta (clearedTail cleared)
        (series - PowerSeries.C (PowerSeries.constantCoeff series))
        nonlinearExponent order (henselDenominatorExponent order - 1)
        etaWeightBound
        (by
          intro parts partsMem index indexMem
          by_cases partZero : parts index = 0
          · rw [partZero]
            simp [clearedTail, generatorWeight]
          · rw [clearedTail, if_neg partZero]
            exact clearedWeight (parts index)
              (nonlinear_supported_part_lt_order series nonlinearExponent order
                (Finset.mem_Icc.mp nonlinearMem).1 parts partsMem index indexMem))
        (fun parts partsMem => nonlinear_supported_exponentBound series
          nonlinearExponent order (Finset.mem_Icc.mp nonlinearMem).1 parts
            partsMem)
    have scalarWeight := integralBranchIteratedWeight_natCast localFactor
      localFactorNeZero ell localBound localCoefficientBound
        (exponent.choose nonlinearExponent)
    have productBound := integralBranchIteratedWeight_mul_five_le localFactor
      localFactorNeZero ell localBound localCoefficientBound
      (coefficientRepresentative exponent 0)
      (exponent.choose nonlinearExponent : IntegralLocalBranch localFactor)
      (leading ^ (degree - exponent))
      (cleared 0 ^ (exponent - nonlinearExponent))
      (regularClearedSupportedPowerCoefficient leading eta
        (clearedTail cleared)
        (series - PowerSeries.C (PowerSeries.constantCoeff series))
        nonlinearExponent order (henselDenominatorExponent order - 1))
    have structural := structuralBudget exponent exponentMem
    have degreeSplit : (exponent - nonlinearExponent) * generatorWeight +
        nonlinearExponent * generatorWeight = exponent * generatorWeight := by
      rw [← Nat.add_mul, Nat.sub_add_cancel nonlinearLe]
    dsimp [generatorWeight] at degreeSplit
    have etaSplit : etaWeight +
        (henselDenominatorExponent order - 1) * etaWeight =
          henselDenominatorExponent order * etaWeight := by
      simpa [Nat.add_mul, add_comm] using congrArg
        (fun exponent => exponent * etaWeight) exponentSplit
    exact productBound.trans <| by
      rw [scalarWeight]
      dsimp [target, generatorWeight]
      omega
  · apply integralBranchIteratedWeight_finset_sum_le localFactor
      localFactorNeZero generatorWeight target
    intro pair pairMem
    have coefficientBound := coefficientWeight exponent exponentMem pair.1
    have leadingPowerBound :=
      (integralBranchIteratedWeight_pow_le localFactor localFactorNeZero ell
        localBound localCoefficientBound leading
          (degree - exponent)).trans
        (Nat.mul_le_mul_left _ leadingWeightBound)
    have powerBound := regularClearedPowerCoefficient_weight_le localFactor
      localFactorNeZero ell localBound etaWeight localCoefficientBound
      leading eta cleared exponent pair.2
        (henselDenominatorExponent order - 1) etaWeightBound
      (by
        intro parts partsMem index indexMem
        have partsSum : ∑ other ∈ Finset.range exponent, parts other =
            pair.2 := (Finset.mem_finsuppAntidiag.mp partsMem).1
        have partLe : parts index ≤ pair.2 := by
          rw [← partsSum]
          exact Finset.single_le_sum
            (fun candidate _ => Nat.zero_le (parts candidate)) indexMem
        have pairSum : pair.1 + pair.2 = order :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp
            (Finset.mem_sdiff.mp pairMem).1
        have pairNe : pair ≠ (0, order) := by
          simpa using (Finset.mem_sdiff.mp pairMem).2
        have secondLt : pair.2 < order := by
          by_contra notLt
          have secondEq : pair.2 = order := by omega
          have firstZero : pair.1 = 0 := by omega
          exact pairNe (Prod.ext firstZero secondEq)
        exact clearedWeight (parts index) (partLe.trans_lt secondLt))
      (fun parts partsMem => positive_shift_exponentBound exponent order pair
        pairMem parts partsMem)
    have productBound := (integralBranchIteratedWeight_mul_le localFactor
      localFactorNeZero ell localBound localCoefficientBound
      (coefficientRepresentative exponent pair.1 *
        leading ^ (degree - exponent))
      (regularClearedPowerCoefficient leading eta cleared exponent pair.2
        (henselDenominatorExponent order - 1))).trans <|
      Nat.add_le_add
        ((integralBranchIteratedWeight_mul_le localFactor localFactorNeZero ell
          localBound localCoefficientBound _ _).trans
          (Nat.add_le_add coefficientBound leadingPowerBound)) powerBound
    have structural := structuralBudget exponent exponentMem
    have etaSplit : etaWeight +
        (henselDenominatorExponent order - 1) * etaWeight =
          henselDenominatorExponent order * etaWeight := by
      simpa [Nat.add_mul, add_comm] using congrArg
        (fun exponent => exponent * etaWeight) exponentSplit
    refine productBound.trans ?_
    change coefficientDegree exponent + (degree - exponent) * leadingWeight +
        (exponent * (localBound + ell - ell * localFactor.natDegree) +
          (henselDenominatorExponent order - 1) * etaWeight) ≤ target
    dsimp [target, generatorWeight]
    omega

/-- Source-support wrapper for the generic fixed-index weight theorem. -/
theorem regularClearedNonlinearEvaluationCoefficient_weight_le
    {K F : Type*} [Field K] [CommRing F] [DecidableEq F]
    (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound etaWeight : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (polynomial : Polynomial (PowerSeries F))
    (coefficientRepresentative : Nat → Nat → IntegralLocalBranch localFactor)
    (coefficientDegree : Nat → Nat)
    (series : PowerSeries F)
    (leading eta : IntegralLocalBranch localFactor)
    (cleared : Nat → IntegralLocalBranch localFactor)
    (degree order leadingWeight : Nat)
    (orderPositive : 0 < order)
    (leadingWeightBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) leading ≤
        leadingWeight)
    (etaWeightBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree) eta ≤ etaWeight)
    (coefficientWeight : ∀ exponent ∈ polynomial.support, ∀ coefficientOrder,
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree)
          (coefficientRepresentative exponent coefficientOrder) ≤
        coefficientDegree exponent)
    (structuralBudget : ∀ exponent ∈ polynomial.support,
      coefficientDegree exponent + (degree - exponent) * leadingWeight +
          exponent * (localBound + ell - ell * localFactor.natDegree) ≤
        (localBound + ell - ell * localFactor.natDegree) + etaWeight)
    (clearedWeight : ∀ coefficientOrder < order,
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree)
          (cleared coefficientOrder) ≤
        (localBound + ell - ell * localFactor.natDegree) +
          henselDenominatorExponent coefficientOrder * etaWeight) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (regularClearedNonlinearEvaluationCoefficient polynomial
          coefficientRepresentative series leading eta cleared degree order) ≤
      (localBound + ell - ell * localFactor.natDegree) +
        henselDenominatorExponent order * etaWeight := by
  simpa only [regularClearedNonlinearEvaluationCoefficient] using
    regularClearedNonlinearEvaluationCoefficientOn_weight_le localFactor
      localFactorNeZero ell localBound etaWeight localCoefficientBound
      polynomial.support coefficientRepresentative coefficientDegree series
      leading eta cleared degree order leadingWeight orderPositive
      leadingWeightBound etaWeightBound coefficientWeight structuralBudget
      clearedWeight

/-! ## Exact V7 positive-order lift -/

/-- The literal regular representative of one shifted coefficient of one
outer-`Y` coefficient of the fixed global branch. -/
def regularLiftedGlobalCoefficient
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    (yExponent coefficientOrder : Nat) :
    IntegralLocalBranch localFactor :=
  AdjoinRoot.of (integralLocalFactor localFactor)
    (shiftedChallengeCoefficient x₀ coefficientOrder
      (globalFactor.coeff yExponent))

theorem integralBranchToFunctionField_regularLiftedGlobalCoefficient
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (yExponent coefficientOrder : Nat) :
    integralBranchToFunctionField localFactor
        (regularLiftedGlobalCoefficient globalFactor x₀ localFactor
          yExponent coefficientOrder) =
      PowerSeries.coeff coefficientOrder
        ((liftedGlobalFactor globalFactor x₀ localFactor).coeff yExponent) := by
  rw [regularLiftedGlobalCoefficient, integralBranchToFunctionField_of,
    coeff_liftedGlobalFactor_coefficient]

/-- The local leading coefficient has the exact residual branch weight
`localBound - ell * deg_Y(H)`. -/
theorem integralBranchIteratedWeight_localLeading_le
    {K : Type*} [Field K] (localFactor : BivariatePolynomial K)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (AdjoinRoot.of (integralLocalFactor localFactor)
          localFactor.leadingCoeff) ≤
      localBound - ell * localFactor.natDegree := by
  have degreeBound := integralBranchIteratedWeight_of_le_natDegree localFactor
    localFactorNeZero ell localBound localCoefficientBound
      localFactor.leadingCoeff
  have leadingBound := localCoefficientBound localFactor.natDegree
    (Polynomial.natDegree_mem_support_of_nonzero localFactorNeZero)
  rw [Polynomial.coeff_natDegree] at leadingBound
  exact degreeBound.trans (by omega)

/-- Every shifted coefficient representative of the exact fixed global
branch is bounded by the literal challenge degree of that outer coefficient. -/
theorem regularLiftedGlobalCoefficient_weight_le
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    (localFactorNeZero : localFactor ≠ 0) (ell localBound : Nat)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (yExponent coefficientOrder : Nat) :
    integralBranchIteratedWeight localFactor localFactorNeZero
        (localBound + ell - ell * localFactor.natDegree)
        (regularLiftedGlobalCoefficient globalFactor x₀ localFactor
          yExponent coefficientOrder) ≤
      (globalFactor.coeff yExponent).natDegree := by
  unfold regularLiftedGlobalCoefficient
  exact integralBranchIteratedWeight_shiftedCoefficient_le localFactor
    localFactorNeZero ell localBound localCoefficientBound x₀ coefficientOrder
      (globalFactor.coeff yExponent)

private theorem mem_global_support_of_mem_lifted_support
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (exponent : Nat)
    (exponentMem : exponent ∈
      (liftedGlobalFactor globalFactor x₀ localFactor).support) :
    exponent ∈ globalFactor.support := by
  rw [Polynomial.mem_support_iff] at exponentMem ⊢
  intro coefficientZero
  apply exponentMem
  rw [liftedGlobalFactor, Polynomial.coeff_map, coefficientZero, map_zero]

/-- Exact natural-number arithmetic behind the repaired branch weight. -/
theorem exact_regularizedHensel_structuralBudget
    (globalFactor : TrivariatePolynomial QM31Exact) (x₀ : QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (ell localBound parentBound : Nat)
    (ellLeParent : ell ≤ parentBound)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (globalCoefficientBound : ∀ exponent ∈ globalFactor.support,
      (globalFactor.coeff exponent).natDegree + ell * exponent ≤ parentBound)
    (exponent : Nat)
    (exponentMem : exponent ∈ globalFactor.support) :
    (globalFactor.coeff exponent).natDegree +
        (globalFactor.natDegree - exponent) *
          (localBound - ell * localFactor.natDegree) +
        exponent *
          (localBound + ell - ell * localFactor.natDegree) ≤
      (localBound + ell - ell * localFactor.natDegree) +
        ((parentBound - ell) + (globalFactor.natDegree - 1) *
          (localBound - ell * localFactor.natDegree)) := by
  let residual := localBound - ell * localFactor.natDegree
  have localDegreeTermLe : ell * localFactor.natDegree ≤ localBound := by
    have bound := localCoefficientBound localFactor.natDegree
      (Polynomial.natDegree_mem_support_of_nonzero localFactorNeZero)
    rw [Polynomial.coeff_natDegree] at bound
    omega
  have generatorIdentity :
      localBound + ell - ell * localFactor.natDegree = residual + ell := by
    dsimp [residual]
    omega
  have exponentLe : exponent ≤ globalFactor.natDegree := by
    exact Polynomial.le_natDegree_of_mem_supp exponent exponentMem
  have coefficientBound := globalCoefficientBound exponent exponentMem
  have exponentResidual :
      (globalFactor.natDegree - exponent) * residual +
          exponent * residual = globalFactor.natDegree * residual := by
    rw [← Nat.add_mul, Nat.sub_add_cancel exponentLe]
  have degreeResidual :
      residual + (globalFactor.natDegree - 1) * residual =
        globalFactor.natDegree * residual := by
    calc
      residual + (globalFactor.natDegree - 1) * residual =
          (globalFactor.natDegree - 1) * residual + 1 * residual := by
        simp [add_comm]
      _ = (globalFactor.natDegree - 1 + 1) * residual := by
        rw [Nat.add_mul]
      _ = _ := by rw [Nat.sub_add_cancel globalFactorPositive]
  have parentSplit : parentBound - ell + ell = parentBound :=
    Nat.sub_add_cancel ellLeParent
  rw [generatorIdentity]
  rw [Nat.mul_add]
  calc
    (globalFactor.coeff exponent).natDegree +
          (globalFactor.natDegree - exponent) * residual +
          (exponent * residual + exponent * ell) =
        ((globalFactor.coeff exponent).natDegree + ell * exponent) +
          ((globalFactor.natDegree - exponent) * residual +
            exponent * residual) := by
      rw [Nat.mul_comm exponent ell]
      ac_rfl
    _ ≤ parentBound + globalFactor.natDegree * residual := by
      exact Nat.add_le_add coefficientBound (le_of_eq exponentResidual)
    _ = parentBound +
          (residual + (globalFactor.natDegree - 1) * residual) := by
      rw [degreeResidual]
    _ = (parentBound - ell + ell) +
          (residual + (globalFactor.natDegree - 1) * residual) := by
      rw [parentSplit]
    _ = (residual + ell) +
          ((parentBound - ell) +
            (globalFactor.natDegree - 1) * residual) := by ac_rfl

/-- One positive recurrence step, separated from the strong induction so the
same literal representative can carry both its image and weight proofs. -/
theorem regularClearedHenselNext_image
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (order : Nat) (orderPositive : 0 < order)
    (cleared : Nat → IntegralLocalBranch localFactor)
    (clearedImage : ∀ lower < order,
      integralBranchToFunctionField localFactor (cleared lower) =
        regularCoefficientMap localFactor localFactor.leadingCoeff *
          integralBranchToFunctionField localFactor
              (regularizedHenselDerivative globalFactor x₀ localFactor) ^
            henselDenominatorExponent lower *
              PowerSeries.coeff lower root) :
    integralBranchToFunctionField localFactor
        (-regularClearedNonlinearEvaluationCoefficientOn globalFactor.support
          (regularLiftedGlobalCoefficient globalFactor x₀ localFactor) root
          (AdjoinRoot.of (integralLocalFactor localFactor)
            localFactor.leadingCoeff)
          (regularizedHenselDerivative globalFactor x₀ localFactor)
          cleared globalFactor.natDegree order) =
      regularCoefficientMap localFactor localFactor.leadingCoeff *
        integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent order *
            PowerSeries.coeff order root := by
  have liftedSupportSubset :
      (liftedGlobalFactor globalFactor x₀ localFactor).support ⊆
        globalFactor.support := by
    intro exponent exponentMem
    exact mem_global_support_of_mem_lifted_support globalFactor x₀
      localFactor exponent exponentMem
  have nonlinearImage := map_regularClearedNonlinearEvaluationCoefficientOn
    (integralBranchToFunctionField localFactor)
    globalFactor.support
    (liftedGlobalFactor globalFactor x₀ localFactor)
    (regularLiftedGlobalCoefficient globalFactor x₀ localFactor) root root
    (AdjoinRoot.of (integralLocalFactor localFactor)
      localFactor.leadingCoeff)
    (regularizedHenselDerivative globalFactor x₀ localFactor)
    cleared globalFactor.natDegree order orderPositive
    (fun exponent exponentMem =>
      Polynomial.le_natDegree_of_mem_supp exponent exponentMem)
    (fun yExponent coefficientOrder =>
      integralBranchToFunctionField_regularLiftedGlobalCoefficient
        globalFactor x₀ localFactor yExponent coefficientOrder)
    (fun lower lowerBound => by
      rw [integralBranchToFunctionField_of]
      exact clearedImage lower lowerBound)
    (fun _ _ nonzero => nonzero)
  have recurrence := exactV7_fixedBranch_coefficient_recurrence
    globalFactor x₀ localFactor root rootEquation rootConstant order
      orderPositive
  have recurrenceOn :
      ((((specializeEvaluationPoint x₀ globalFactor).derivative).map
          (algebraMap (Polynomial QM31Exact)
            (ChallengeRationalField QM31Exact))).map
        (AdjoinRoot.of (localFactorOverRational localFactor))).eval
          (AdjoinRoot.root (localFactorOverRational localFactor)) *
        PowerSeries.coeff order root =
      -nonlinearEvaluationCoefficientOn globalFactor.support
        (liftedGlobalFactor globalFactor x₀ localFactor) root order := by
    rw [nonlinearEvaluationCoefficientOn_eq globalFactor.support
      (liftedGlobalFactor globalFactor x₀ localFactor) root order
        liftedSupportSubset]
    exact recurrence
  have etaImage := integralBranchToFunctionField_regularizedHenselDerivative
    globalFactor x₀ localFactor
  have derivativeValueEquality :
      (specializeEvaluationPoint x₀ globalFactor).derivative.eval₂
          (regularCoefficientMap localFactor)
          (AdjoinRoot.root (localFactorOverRational localFactor)) =
        ((((specializeEvaluationPoint x₀ globalFactor).derivative).map
            (algebraMap (Polynomial QM31Exact)
              (ChallengeRationalField QM31Exact))).map
          (AdjoinRoot.of (localFactorOverRational localFactor))).eval
            (AdjoinRoot.root (localFactorOverRational localFactor)) := by
    simp [Polynomial.eval₂_eq_eval_map, regularCoefficientMap,
      Polynomial.map_map]
  have etaImage' :
      integralBranchToFunctionField localFactor
          (regularizedHenselDerivative globalFactor x₀ localFactor) =
        regularCoefficientMap localFactor localFactor.leadingCoeff ^
            (globalFactor.natDegree - 1) *
          ((((specializeEvaluationPoint x₀ globalFactor).derivative).map
              (algebraMap (Polynomial QM31Exact)
                (ChallengeRationalField QM31Exact))).map
            (AdjoinRoot.of (localFactorOverRational localFactor))).eval
              (AdjoinRoot.root (localFactorOverRational localFactor)) := by
    rw [etaImage, derivativeValueEquality]
  have degreeSplit : globalFactor.natDegree - 1 + 1 =
      globalFactor.natDegree := Nat.sub_add_cancel globalFactorPositive
  have exponentSplit : henselDenominatorExponent order - 1 + 1 =
      henselDenominatorExponent order := by
    unfold henselDenominatorExponent
    omega
  have nonlinearEquality :
      nonlinearEvaluationCoefficientOn globalFactor.support
          (liftedGlobalFactor globalFactor x₀ localFactor) root order =
        -(((((specializeEvaluationPoint x₀ globalFactor).derivative).map
              (algebraMap (Polynomial QM31Exact)
                (ChallengeRationalField QM31Exact))).map
            (AdjoinRoot.of (localFactorOverRational localFactor))).eval
              (AdjoinRoot.root (localFactorOverRational localFactor)) *
          PowerSeries.coeff order root) := by
    calc
      nonlinearEvaluationCoefficientOn globalFactor.support
          (liftedGlobalFactor globalFactor x₀ localFactor) root order =
          -(-nonlinearEvaluationCoefficientOn globalFactor.support
            (liftedGlobalFactor globalFactor x₀ localFactor) root order) := by
        ring
      _ = _ := by rw [← recurrenceOn]
  rw [map_neg, nonlinearImage, integralBranchToFunctionField_of]
  have leadingPower :
      regularCoefficientMap localFactor localFactor.leadingCoeff *
          regularCoefficientMap localFactor localFactor.leadingCoeff ^
            (globalFactor.natDegree - 1) =
        regularCoefficientMap localFactor localFactor.leadingCoeff ^
          globalFactor.natDegree := by
    calc
      regularCoefficientMap localFactor localFactor.leadingCoeff *
          regularCoefficientMap localFactor localFactor.leadingCoeff ^
            (globalFactor.natDegree - 1) =
        regularCoefficientMap localFactor localFactor.leadingCoeff ^
            (globalFactor.natDegree - 1) *
          regularCoefficientMap localFactor localFactor.leadingCoeff :=
        mul_comm _ _
      _ = regularCoefficientMap localFactor localFactor.leadingCoeff ^
          (globalFactor.natDegree - 1 + 1) := (pow_succ _ _).symm
      _ = _ := by rw [degreeSplit]
  have etaPower :
      integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent order =
        integralBranchToFunctionField localFactor
              (regularizedHenselDerivative globalFactor x₀ localFactor) ^
            (henselDenominatorExponent order - 1) *
          integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) := by
    calc
      integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          henselDenominatorExponent order =
        integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          (henselDenominatorExponent order - 1 + 1) := by
        rw [exponentSplit]
      _ = _ := pow_succ _ _
  have targetRewrite :
      regularCoefficientMap localFactor localFactor.leadingCoeff *
          integralBranchToFunctionField localFactor
              (regularizedHenselDerivative globalFactor x₀ localFactor) ^
            henselDenominatorExponent order *
          PowerSeries.coeff order root =
        regularCoefficientMap localFactor localFactor.leadingCoeff ^
            globalFactor.natDegree *
          integralBranchToFunctionField localFactor
              (regularizedHenselDerivative globalFactor x₀ localFactor) ^
            (henselDenominatorExponent order - 1) *
          (((((specializeEvaluationPoint x₀ globalFactor).derivative).map
              (algebraMap (Polynomial QM31Exact)
                (ChallengeRationalField QM31Exact))).map
            (AdjoinRoot.of (localFactorOverRational localFactor))).eval
              (AdjoinRoot.root (localFactorOverRational localFactor)) *
            PowerSeries.coeff order root) := by
    rw [etaPower]
    calc
      regularCoefficientMap localFactor localFactor.leadingCoeff *
            (integralBranchToFunctionField localFactor
                (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                (henselDenominatorExponent order - 1) *
              integralBranchToFunctionField localFactor
                (regularizedHenselDerivative globalFactor x₀ localFactor)) *
            PowerSeries.coeff order root =
          (regularCoefficientMap localFactor localFactor.leadingCoeff *
              regularCoefficientMap localFactor localFactor.leadingCoeff ^
                (globalFactor.natDegree - 1)) *
            integralBranchToFunctionField localFactor
                (regularizedHenselDerivative globalFactor x₀ localFactor) ^
              (henselDenominatorExponent order - 1) *
            (((((specializeEvaluationPoint x₀ globalFactor).derivative).map
                (algebraMap (Polynomial QM31Exact)
                  (ChallengeRationalField QM31Exact))).map
              (AdjoinRoot.of (localFactorOverRational localFactor))).eval
                (AdjoinRoot.root (localFactorOverRational localFactor)) *
              PowerSeries.coeff order root) := by
        rw [etaImage']
        ring
      _ = _ := by rw [leadingPower]
  calc
    -(regularCoefficientMap localFactor localFactor.leadingCoeff ^
          globalFactor.natDegree *
        integralBranchToFunctionField localFactor
            (regularizedHenselDerivative globalFactor x₀ localFactor) ^
          (henselDenominatorExponent order - 1) *
        nonlinearEvaluationCoefficientOn globalFactor.support
          (liftedGlobalFactor globalFactor x₀ localFactor) root order) =
        regularCoefficientMap localFactor localFactor.leadingCoeff ^
            globalFactor.natDegree *
          integralBranchToFunctionField localFactor
              (regularizedHenselDerivative globalFactor x₀ localFactor) ^
            (henselDenominatorExponent order - 1) *
          (((((specializeEvaluationPoint x₀ globalFactor).derivative).map
              (algebraMap (Polynomial QM31Exact)
                (ChallengeRationalField QM31Exact))).map
            (AdjoinRoot.of (localFactorOverRational localFactor))).eval
              (AdjoinRoot.root (localFactorOverRational localFactor)) *
            PowerSeries.coeff order root) := by
      rw [nonlinearEquality]
      ring
    _ = _ := targetRewrite.symm

/-- Every coefficient of the exact fixed-branch Hensel root admits a literal
regular representative after multiplication by `W * eta^(2t-1)`.  The
construction is by strong induction and uses only lower root coefficients in
the nonlinear recurrence. -/
theorem exists_regularClearedHenselCoefficient
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (order : Nat) :
    ∃ cleared : IntegralLocalBranch localFactor,
      integralBranchToFunctionField localFactor cleared =
        regularCoefficientMap localFactor localFactor.leadingCoeff *
          integralBranchToFunctionField localFactor
              (regularizedHenselDerivative globalFactor x₀ localFactor) ^
            henselDenominatorExponent order *
              PowerSeries.coeff order root := by
  induction order using Nat.strong_induction_on with
  | h order induction =>
      by_cases orderZero : order = 0
      · subst order
        exact ⟨regularClearedHenselCoefficientZero localFactor,
          integralBranchToFunctionField_regularClearedHenselCoefficientZero
            localFactor root rootConstant
              (regularizedHenselDerivative globalFactor x₀ localFactor)⟩
      · have orderPositive : 0 < order := Nat.pos_of_ne_zero orderZero
        let cleared : Nat → IntegralLocalBranch localFactor := fun lower =>
          if lowerBound : lower < order then
            Classical.choose (induction lower lowerBound)
          else 0
        have clearedImage : ∀ lower < order,
            integralBranchToFunctionField localFactor (cleared lower) =
              regularCoefficientMap localFactor localFactor.leadingCoeff *
                integralBranchToFunctionField localFactor
                    (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                  henselDenominatorExponent lower *
                    PowerSeries.coeff lower root := by
          intro lower lowerBound
          simp only [cleared, dif_pos lowerBound]
          exact (Classical.choose_spec (induction lower lowerBound))
        let coefficientRepresentative : Nat → Nat →
            IntegralLocalBranch localFactor :=
          regularLiftedGlobalCoefficient globalFactor x₀ localFactor
        let nonlinearRepresentative :=
          regularClearedNonlinearEvaluationCoefficientOn globalFactor.support
            coefficientRepresentative root
            (AdjoinRoot.of (integralLocalFactor localFactor)
              localFactor.leadingCoeff)
            (regularizedHenselDerivative globalFactor x₀ localFactor)
            cleared globalFactor.natDegree order
        let next : IntegralLocalBranch localFactor := -nonlinearRepresentative
        refine ⟨next, ?_⟩
        have liftedSupportSubset :
            (liftedGlobalFactor globalFactor x₀ localFactor).support ⊆
              globalFactor.support := by
          intro exponent exponentMem
          exact mem_global_support_of_mem_lifted_support globalFactor x₀
            localFactor exponent exponentMem
        have nonlinearImage :=
          map_regularClearedNonlinearEvaluationCoefficientOn
            (integralBranchToFunctionField localFactor)
            globalFactor.support
            (liftedGlobalFactor globalFactor x₀ localFactor)
            coefficientRepresentative root root
            (AdjoinRoot.of (integralLocalFactor localFactor)
              localFactor.leadingCoeff)
            (regularizedHenselDerivative globalFactor x₀ localFactor)
            cleared globalFactor.natDegree order orderPositive
            (fun exponent exponentMem =>
              Polynomial.le_natDegree_of_mem_supp exponent exponentMem)
            (fun yExponent coefficientOrder =>
              integralBranchToFunctionField_regularLiftedGlobalCoefficient
                globalFactor x₀ localFactor yExponent coefficientOrder)
            (fun lower lowerBound => by
              rw [integralBranchToFunctionField_of]
              exact clearedImage lower lowerBound)
            (fun _ _ nonzero => nonzero)
        have recurrence := exactV7_fixedBranch_coefficient_recurrence
          globalFactor x₀ localFactor root rootEquation rootConstant order
            orderPositive
        have recurrenceOn :
            ((((specializeEvaluationPoint x₀ globalFactor).derivative).map
                (algebraMap (Polynomial QM31Exact)
                  (ChallengeRationalField QM31Exact))).map
              (AdjoinRoot.of (localFactorOverRational localFactor))).eval
                (AdjoinRoot.root (localFactorOverRational localFactor)) *
              PowerSeries.coeff order root =
            -nonlinearEvaluationCoefficientOn globalFactor.support
              (liftedGlobalFactor globalFactor x₀ localFactor) root order := by
          rw [nonlinearEvaluationCoefficientOn_eq globalFactor.support
            (liftedGlobalFactor globalFactor x₀ localFactor) root order
              liftedSupportSubset]
          exact recurrence
        have etaImage :=
          integralBranchToFunctionField_regularizedHenselDerivative
            globalFactor x₀ localFactor
        have derivativeValueEquality :
            (specializeEvaluationPoint x₀ globalFactor).derivative.eval₂
                (regularCoefficientMap localFactor)
                (AdjoinRoot.root (localFactorOverRational localFactor)) =
              ((((specializeEvaluationPoint x₀ globalFactor).derivative).map
                  (algebraMap (Polynomial QM31Exact)
                    (ChallengeRationalField QM31Exact))).map
                (AdjoinRoot.of (localFactorOverRational localFactor))).eval
                  (AdjoinRoot.root
                    (localFactorOverRational localFactor)) := by
          simp [Polynomial.eval₂_eq_eval_map, regularCoefficientMap,
            Polynomial.map_map]
        have etaImage' :
            integralBranchToFunctionField localFactor
                (regularizedHenselDerivative globalFactor x₀ localFactor) =
              regularCoefficientMap localFactor localFactor.leadingCoeff ^
                  (globalFactor.natDegree - 1) *
                ((((specializeEvaluationPoint x₀ globalFactor).derivative).map
                    (algebraMap (Polynomial QM31Exact)
                      (ChallengeRationalField QM31Exact))).map
                  (AdjoinRoot.of (localFactorOverRational localFactor))).eval
                    (AdjoinRoot.root
                      (localFactorOverRational localFactor)) := by
          rw [etaImage, derivativeValueEquality]
        have degreeSplit : globalFactor.natDegree - 1 + 1 =
            globalFactor.natDegree := Nat.sub_add_cancel globalFactorPositive
        have exponentSplit : henselDenominatorExponent order - 1 + 1 =
            henselDenominatorExponent order := by
          unfold henselDenominatorExponent
          omega
        have nonlinearEquality :
            nonlinearEvaluationCoefficientOn globalFactor.support
                (liftedGlobalFactor globalFactor x₀ localFactor) root order =
              -(((((specializeEvaluationPoint x₀ globalFactor).derivative).map
                    (algebraMap (Polynomial QM31Exact)
                      (ChallengeRationalField QM31Exact))).map
                  (AdjoinRoot.of (localFactorOverRational localFactor))).eval
                    (AdjoinRoot.root (localFactorOverRational localFactor)) *
                PowerSeries.coeff order root) := by
          calc
            nonlinearEvaluationCoefficientOn globalFactor.support
                (liftedGlobalFactor globalFactor x₀ localFactor) root order =
                -(-nonlinearEvaluationCoefficientOn globalFactor.support
                  (liftedGlobalFactor globalFactor x₀ localFactor) root order) :=
              by ring
            _ = _ := by rw [← recurrenceOn]
        change integralBranchToFunctionField localFactor
            (-nonlinearRepresentative) = _
        rw [map_neg, nonlinearImage]
        rw [integralBranchToFunctionField_of]
        have leadingPower :
            regularCoefficientMap localFactor localFactor.leadingCoeff *
                regularCoefficientMap localFactor localFactor.leadingCoeff ^
                  (globalFactor.natDegree - 1) =
              regularCoefficientMap localFactor localFactor.leadingCoeff ^
                globalFactor.natDegree := by
          calc
            regularCoefficientMap localFactor localFactor.leadingCoeff *
                regularCoefficientMap localFactor localFactor.leadingCoeff ^
                  (globalFactor.natDegree - 1) =
              regularCoefficientMap localFactor localFactor.leadingCoeff ^
                  (globalFactor.natDegree - 1) *
                regularCoefficientMap localFactor localFactor.leadingCoeff :=
              mul_comm _ _
            _ = regularCoefficientMap localFactor localFactor.leadingCoeff ^
                (globalFactor.natDegree - 1 + 1) :=
              (pow_succ _ _).symm
            _ = _ := by rw [degreeSplit]
        have etaPower :
            integralBranchToFunctionField localFactor
                  (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                henselDenominatorExponent order =
              integralBranchToFunctionField localFactor
                    (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                  (henselDenominatorExponent order - 1) *
                integralBranchToFunctionField localFactor
                  (regularizedHenselDerivative globalFactor x₀ localFactor) := by
          calc
            integralBranchToFunctionField localFactor
                  (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                henselDenominatorExponent order =
              integralBranchToFunctionField localFactor
                  (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                (henselDenominatorExponent order - 1 + 1) := by
              rw [exponentSplit]
            _ = _ := pow_succ _ _
        have targetRewrite :
            regularCoefficientMap localFactor localFactor.leadingCoeff *
                integralBranchToFunctionField localFactor
                    (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                  henselDenominatorExponent order *
                PowerSeries.coeff order root =
              regularCoefficientMap localFactor localFactor.leadingCoeff ^
                  globalFactor.natDegree *
                integralBranchToFunctionField localFactor
                    (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                  (henselDenominatorExponent order - 1) *
                (((((specializeEvaluationPoint x₀ globalFactor).derivative).map
                    (algebraMap (Polynomial QM31Exact)
                      (ChallengeRationalField QM31Exact))).map
                  (AdjoinRoot.of (localFactorOverRational localFactor))).eval
                    (AdjoinRoot.root (localFactorOverRational localFactor)) *
                  PowerSeries.coeff order root) := by
          calc
            regularCoefficientMap localFactor localFactor.leadingCoeff *
                  integralBranchToFunctionField localFactor
                      (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                    henselDenominatorExponent order *
                  PowerSeries.coeff order root =
                regularCoefficientMap localFactor localFactor.leadingCoeff *
                  (integralBranchToFunctionField localFactor
                      (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                      (henselDenominatorExponent order - 1) *
                    integralBranchToFunctionField localFactor
                      (regularizedHenselDerivative globalFactor x₀ localFactor)) *
                  PowerSeries.coeff order root := by
              rw [etaPower]
            _ = (regularCoefficientMap localFactor localFactor.leadingCoeff *
                    regularCoefficientMap localFactor
                        localFactor.leadingCoeff ^
                      (globalFactor.natDegree - 1)) *
                  integralBranchToFunctionField localFactor
                      (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                    (henselDenominatorExponent order - 1) *
                  (((((specializeEvaluationPoint x₀ globalFactor).derivative).map
                      (algebraMap (Polynomial QM31Exact)
                        (ChallengeRationalField QM31Exact))).map
                    (AdjoinRoot.of (localFactorOverRational localFactor))).eval
                      (AdjoinRoot.root
                        (localFactorOverRational localFactor)) *
                    PowerSeries.coeff order root) := by
              rw [etaImage']
              ring
            _ = _ := by rw [leadingPower]
        calc
          -(regularCoefficientMap localFactor localFactor.leadingCoeff ^
                globalFactor.natDegree *
              integralBranchToFunctionField localFactor
                  (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                (henselDenominatorExponent order - 1) *
              nonlinearEvaluationCoefficientOn globalFactor.support
                (liftedGlobalFactor globalFactor x₀ localFactor) root order) =
              regularCoefficientMap localFactor localFactor.leadingCoeff ^
                  globalFactor.natDegree *
                integralBranchToFunctionField localFactor
                    (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                  (henselDenominatorExponent order - 1) *
                (((((specializeEvaluationPoint x₀ globalFactor).derivative).map
                    (algebraMap (Polynomial QM31Exact)
                      (ChallengeRationalField QM31Exact))).map
                  (AdjoinRoot.of (localFactorOverRational localFactor))).eval
                    (AdjoinRoot.root (localFactorOverRational localFactor)) *
                  PowerSeries.coeff order root) := by
            rw [nonlinearEquality]
            ring
          _ = _ := targetRewrite.symm

/-- Image and weight simultaneously, for the exact fixed V7 branch.  This is
the terminal repaired form of BCIKS Claim A.2 used by the zero-count stage. -/
theorem exists_regularClearedHenselCoefficient_with_weight
    (globalFactor : TrivariatePolynomial QM31Exact)
    (globalFactorPositive : 0 < globalFactor.natDegree)
    (x₀ : QM31Exact)
    (localFactor : BivariatePolynomial QM31Exact)
    [Fact (Irreducible (localFactorOverRational localFactor))]
    (localFactorNeZero : localFactor ≠ 0)
    (ell localBound parentBound : Nat)
    (ellLeParent : ell ≤ parentBound)
    (localCoefficientBound : ∀ exponent ∈ localFactor.support,
      (localFactor.coeff exponent).natDegree + ell * exponent ≤ localBound)
    (globalCoefficientBound : ∀ exponent ∈ globalFactor.support,
      (globalFactor.coeff exponent).natDegree + ell * exponent ≤ parentBound)
    (root : PowerSeries (LocalBranchField localFactor))
    (rootEquation :
      (liftedGlobalFactor globalFactor x₀ localFactor).IsRoot root)
    (rootConstant : PowerSeries.constantCoeff root =
      AdjoinRoot.root (localFactorOverRational localFactor))
    (order : Nat) :
    let etaWeight := (parentBound - ell) +
      (globalFactor.natDegree - 1) *
        (localBound - ell * localFactor.natDegree)
    ∃ cleared : IntegralLocalBranch localFactor,
      integralBranchToFunctionField localFactor cleared =
          regularCoefficientMap localFactor localFactor.leadingCoeff *
            integralBranchToFunctionField localFactor
                (regularizedHenselDerivative globalFactor x₀ localFactor) ^
              henselDenominatorExponent order *
                PowerSeries.coeff order root ∧
        integralBranchIteratedWeight localFactor localFactorNeZero
            (localBound + ell - ell * localFactor.natDegree) cleared ≤
          (localBound + ell - ell * localFactor.natDegree) +
            henselDenominatorExponent order * etaWeight := by
  dsimp only
  let etaWeight := (parentBound - ell) +
    (globalFactor.natDegree - 1) *
      (localBound - ell * localFactor.natDegree)
  have parentCoefficientBound : ∀ exponent ∈
      (specializeEvaluationPoint x₀ globalFactor).support,
      ((specializeEvaluationPoint x₀ globalFactor).coeff exponent).natDegree +
        ell * exponent ≤ parentBound := by
    intro exponent exponentMem
    have globalMem : exponent ∈ globalFactor.support := by
      rw [Polynomial.mem_support_iff] at exponentMem ⊢
      intro coefficientZero
      apply exponentMem
      simp [specializeEvaluationPoint, coefficientZero]
    exact (Nat.add_le_add_right
      (by
        simpa [specializeEvaluationPoint, evaluateInnerVariable] using
          (Polynomial.natDegree_map_le
            (p := globalFactor.coeff exponent)
            (f := Polynomial.evalRingHom x₀))) (ell * exponent)).trans
      (globalCoefficientBound exponent globalMem)
  have etaWeightBound :
      integralBranchIteratedWeight localFactor localFactorNeZero
          (localBound + ell - ell * localFactor.natDegree)
          (regularizedHenselDerivative globalFactor x₀ localFactor) ≤
        etaWeight := by
    exact integralBranchIteratedWeight_regularizedHenselDerivative_le
      globalFactor x₀ localFactor localFactorNeZero ell localBound parentBound
        localCoefficientBound parentCoefficientBound
  induction order using Nat.strong_induction_on with
  | h order induction =>
      by_cases orderZero : order = 0
      · subst order
        refine ⟨regularClearedHenselCoefficientZero localFactor,
          integralBranchToFunctionField_regularClearedHenselCoefficientZero
            localFactor root rootConstant
              (regularizedHenselDerivative globalFactor x₀ localFactor), ?_⟩
        simpa [etaWeight] using
          regularClearedHenselCoefficientZero_weight_le localFactor
            localFactorNeZero ell localBound localCoefficientBound
      · have orderPositive : 0 < order := Nat.pos_of_ne_zero orderZero
        let cleared : Nat → IntegralLocalBranch localFactor := fun lower =>
          if lowerBound : lower < order then
            Classical.choose (induction lower lowerBound)
          else 0
        have clearedImage : ∀ lower < order,
            integralBranchToFunctionField localFactor (cleared lower) =
              regularCoefficientMap localFactor localFactor.leadingCoeff *
                integralBranchToFunctionField localFactor
                    (regularizedHenselDerivative globalFactor x₀ localFactor) ^
                  henselDenominatorExponent lower *
                    PowerSeries.coeff lower root := by
          intro lower lowerBound
          simp only [cleared, dif_pos lowerBound]
          exact (Classical.choose_spec (induction lower lowerBound)).1
        have clearedWeight : ∀ lower < order,
            integralBranchIteratedWeight localFactor localFactorNeZero
                (localBound + ell - ell * localFactor.natDegree)
                (cleared lower) ≤
              (localBound + ell - ell * localFactor.natDegree) +
                henselDenominatorExponent lower * etaWeight := by
          intro lower lowerBound
          simp only [cleared, dif_pos lowerBound]
          exact (Classical.choose_spec (induction lower lowerBound)).2
        let nonlinearRepresentative :=
          regularClearedNonlinearEvaluationCoefficientOn globalFactor.support
            (regularLiftedGlobalCoefficient globalFactor x₀ localFactor) root
            (AdjoinRoot.of (integralLocalFactor localFactor)
              localFactor.leadingCoeff)
            (regularizedHenselDerivative globalFactor x₀ localFactor)
            cleared globalFactor.natDegree order
        refine ⟨-nonlinearRepresentative,
          regularClearedHenselNext_image globalFactor globalFactorPositive x₀
            localFactor root rootEquation rootConstant order orderPositive
            cleared clearedImage, ?_⟩
        rw [integralBranchIteratedWeight_neg]
        exact regularClearedNonlinearEvaluationCoefficientOn_weight_le
          localFactor localFactorNeZero ell localBound etaWeight
          localCoefficientBound
          globalFactor.support
          (regularLiftedGlobalCoefficient globalFactor x₀ localFactor)
          (fun exponent => (globalFactor.coeff exponent).natDegree)
          root
          (AdjoinRoot.of (integralLocalFactor localFactor)
            localFactor.leadingCoeff)
          (regularizedHenselDerivative globalFactor x₀ localFactor)
          cleared globalFactor.natDegree order
          (localBound - ell * localFactor.natDegree) orderPositive
          (integralBranchIteratedWeight_localLeading_le localFactor
            localFactorNeZero ell localBound localCoefficientBound)
          etaWeightBound
          (fun exponent _ coefficientOrder =>
            regularLiftedGlobalCoefficient_weight_le globalFactor x₀
              localFactor localFactorNeZero ell localBound
              localCoefficientBound exponent coefficientOrder)
          (fun exponent exponentMem =>
            exact_regularizedHensel_structuralBudget globalFactor x₀
              globalFactorPositive localFactor localFactorNeZero ell localBound
              parentBound ellLeParent localCoefficientBound
              globalCoefficientBound exponent exponentMem)
          clearedWeight

#print axioms map_clearedTail
#print axioms nonlinear_supported_exponentBound
#print axioms positive_shift_exponentBound
#print axioms map_regularClearedNonlinearEvaluationCoefficient
#print axioms map_regularClearedNonlinearEvaluationCoefficientOn
#print axioms map_neg_regularClearedNonlinearEvaluationCoefficientOn_of_isRoot
#print axioms map_neg_regularClearedNonlinearEvaluationCoefficient_of_isRoot
#print axioms regularClearedNonlinearEvaluationCoefficient_weight_le
#print axioms integralBranchToFunctionField_regularLiftedGlobalCoefficient
#print axioms integralBranchIteratedWeight_localLeading_le
#print axioms regularLiftedGlobalCoefficient_weight_le
#print axioms exact_regularizedHensel_structuralBudget
#print axioms regularClearedHenselNext_image
#print axioms exists_regularClearedHenselCoefficient
#print axioms exists_regularClearedHenselCoefficient_with_weight

end

end AspisK1.V7ExactCorrelatedAgreementHenselIntegralLift
