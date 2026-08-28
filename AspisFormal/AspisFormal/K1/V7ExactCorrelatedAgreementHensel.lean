import AspisFormal.K1.V7ExactCorrelatedAgreementSmooth
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Characteristic-free Hensel extraction used by exact V7 correlated agreement

This module starts the lifting step over a formal power-series ring.  The
simple-root hypotheses are literal constant-coefficient statements; no
characteristic-zero derivative rule is used.  The completion theorem in
mathlib supplies Hensel existence for `L⟦T⟧` at `(T)`.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreementHensel

open Polynomial
open scoped Ring

noncomputable section

/-- The Newton argument underlying adic Hensel lifting does not need the
polynomial to be monic when a simple approximate root is already supplied.
Mathlib's `HenselianRing` interface requests monicity because it packages a
stronger general-purpose convention; this exact lemma records the form used
by the correlated-agreement proof. -/
theorem exists_adic_root_of_simple_approximation
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (polynomial : R[X]) (approximation : R)
    (rootModuloIdeal : polynomial.eval approximation ∈ I)
    (derivativeUnitModuloIdeal : IsUnit
      (Ideal.Quotient.mk I (polynomial.derivative.eval approximation))) :
    ∃ root : R, polynomial.IsRoot root ∧ root - approximation ∈ I := by
  classical
  let derivativePolynomial := derivative polynomial
  let approximations : ℕ → R := fun n => Nat.recOn n approximation fun _ value =>
    value - polynomial.eval value *
      (derivativePolynomial.eval value)⁻¹ʳ
  have approximationStep : ∀ n, approximations (n + 1) =
      approximations n - polynomial.eval (approximations n) *
        (derivativePolynomial.eval (approximations n))⁻¹ʳ := by
    intro n
    simp only [approximations]
  have congruentToInitial : ∀ n,
      approximations n ≡ approximation [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n induction =>
      rw [approximationStep, sub_eq_add_neg, ← add_zero approximation]
      refine induction.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at rootModuloIdeal ⊢
      exact (induction.eval polynomial).trans rootModuloIdeal
  have derivativeUnits : ∀ n,
      IsUnit (derivativePolynomial.eval (approximations n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I
      (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert derivativeUnitModuloIdeal using 1
    exact SModEq.def.mp ((congruentToInitial n).eval _)
  have evaluationPower : ∀ n,
      polynomial.eval (approximations n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      change polynomial.eval approximation ∈ I ^ (0 + 1)
      simpa only [zero_add, pow_one] using rootModuloIdeal
    | succ n induction =>
      rw [← taylor_eval_sub (approximations n), approximationStep,
        sub_eq_add_neg, sub_eq_add_neg, add_neg_cancel_comm]
      rw [eval_eq_sum,
        sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),
        ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, taylor_coeff_zero,
          taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (derivativeUnits n),
          mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨twoLe, _⟩
        have powerLe : n + 2 ≤ i * (n + 1) := by
          nlinarith only [twoLe]
        refine Ideal.mul_mem_left _ _
          (Ideal.pow_le_pow_right powerLe ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow
          ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ induction) _
  have cauchy : ∀ m n, m ≤ n →
      approximations m ≡ approximations n
        [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n less
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le less
    clear less
    induction k with
    | zero => rw [add_zero]
    | succ k induction =>
      rw [← add_assoc, approximationStep,
        ← add_zero (approximations m), sub_eq_add_neg]
      refine induction.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _
        (Ideal.pow_le_pow_right ?_ (evaluationPower _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨root, limit⟩ := IsPrecomplete.prec' approximations (cauchy _ _)
  refine ⟨root, ?_, ?_⟩
  · show polynomial.IsRoot root
    suffices ∀ n, polynomial.eval root ≡ 0
        [SMOD (I ^ n • ⊤ : Ideal R)] by
      exact IsHausdorff.haus' _ this
    intro n
    specialize limit n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at limit ⊢
    refine (limit.symm.eval polynomial).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (evaluationPower _)
  · specialize limit (0 + 1)
    rw [approximationStep, pow_one, ← Ideal.one_eq_top,
      Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at limit
    rw [← SModEq.sub_mem, ← add_zero approximation]
    refine limit.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ rootModuloIdeal

/-- Exact non-monic simple-root Hensel lifting over a power-series ring. -/
theorem exists_powerSeries_root_of_simple_constant_root
    {L : Type*} [Field L]
    (polynomial : Polynomial (PowerSeries L)) (constantRoot : L)
    (rootModuloVariable : PowerSeries.constantCoeff
      (polynomial.eval (PowerSeries.C constantRoot)) = 0)
    (derivativeModuloVariableNeZero : PowerSeries.constantCoeff
      (polynomial.derivative.eval (PowerSeries.C constantRoot)) ≠ 0) :
    ∃ root : PowerSeries L,
      polynomial.IsRoot root ∧
        PowerSeries.constantCoeff root = constantRoot := by
  let variableIdeal : Ideal (PowerSeries L) :=
    Ideal.span {PowerSeries.X}
  have rootMem : polynomial.eval (PowerSeries.C constantRoot) ∈
      variableIdeal := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    exact rootModuloVariable
  have derivativeUnit : IsUnit
      (polynomial.derivative.eval (PowerSeries.C constantRoot)) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr
      (Ne.isUnit derivativeModuloVariableNeZero)
  have quotientDerivativeUnit : IsUnit
      (Ideal.Quotient.mk variableIdeal
        (polynomial.derivative.eval (PowerSeries.C constantRoot))) :=
    derivativeUnit.map (Ideal.Quotient.mk variableIdeal)
  obtain ⟨root, rootEquation, rootCongruent⟩ :=
    exists_adic_root_of_simple_approximation variableIdeal polynomial
      (PowerSeries.C constantRoot) rootMem quotientDerivativeUnit
  refine ⟨root, rootEquation, ?_⟩
  have constantDifference : PowerSeries.constantCoeff
      (root - PowerSeries.C constantRoot) = 0 := by
    rw [← PowerSeries.X_dvd_iff, ← Ideal.mem_span_singleton]
    exact rootCongruent
  rw [map_sub, PowerSeries.constantCoeff_C] at constantDifference
  exact sub_eq_zero.mp constantDifference

/-- The simple lift with a fixed constant coefficient is unique.  This is
the equality used later when a challenge-dependent polynomial root is mapped
into the same complete local ring. -/
theorem powerSeries_root_unique_of_simple_constant_root
    {L : Type*} [Field L]
    (polynomial : Polynomial (PowerSeries L)) (constantRoot : L)
    (derivativeModuloVariableNeZero : PowerSeries.constantCoeff
      (polynomial.derivative.eval (PowerSeries.C constantRoot)) ≠ 0)
    (left right : PowerSeries L)
    (leftRoot : polynomial.IsRoot left)
    (rightRoot : polynomial.IsRoot right)
    (leftConstant : PowerSeries.constantCoeff left = constantRoot)
    (rightConstant : PowerSeries.constantCoeff right = constantRoot) :
    left = right := by
  have derivativeConstant : PowerSeries.constantCoeff
      (polynomial.derivative.eval left) =
        PowerSeries.constantCoeff
          (polynomial.derivative.eval (PowerSeries.C constantRoot)) := by
    rw [← Polynomial.eval₂_id, ← Polynomial.eval₂_id,
      Polynomial.hom_eval₂, Polynomial.hom_eval₂,
      leftConstant, PowerSeries.constantCoeff_C]
  have derivativeUnit : IsUnit (polynomial.derivative.eval left) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr <| by
      rw [derivativeConstant]
      exact Ne.isUnit derivativeModuloVariableNeZero
  have differenceNotUnit : ¬ IsUnit (left - right) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [map_sub, leftConstant, rightConstant, sub_self]
    exact not_isUnit_zero
  exact IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    leftRoot.eq_zero rightRoot.eq_zero differenceNotUnit derivativeUnit

/-- A monic polynomial over `L⟦T⟧` with a simple root after reduction modulo
`T` has a power-series root with exactly that constant coefficient. -/
theorem exists_powerSeries_root_of_monic_simple_constant_root
    {L : Type*} [Field L]
    (polynomial : Polynomial (PowerSeries L))
    (polynomialMonic : polynomial.Monic) (constantRoot : L)
    (rootModuloVariable : PowerSeries.constantCoeff
      (polynomial.eval (PowerSeries.C constantRoot)) = 0)
    (derivativeModuloVariableNeZero : PowerSeries.constantCoeff
      (polynomial.derivative.eval (PowerSeries.C constantRoot)) ≠ 0) :
    ∃ root : PowerSeries L,
      polynomial.IsRoot root ∧
        PowerSeries.constantCoeff root = constantRoot := by
  let variableIdeal : Ideal (PowerSeries L) :=
    Ideal.span {PowerSeries.X}
  have rootMem : polynomial.eval (PowerSeries.C constantRoot) ∈
      variableIdeal := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    exact rootModuloVariable
  have derivativeUnit : IsUnit
      (polynomial.derivative.eval (PowerSeries.C constantRoot)) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr
      (Ne.isUnit derivativeModuloVariableNeZero)
  have quotientDerivativeUnit : IsUnit
      (Ideal.Quotient.mk variableIdeal
        (polynomial.derivative.eval (PowerSeries.C constantRoot))) :=
    derivativeUnit.map (Ideal.Quotient.mk variableIdeal)
  obtain ⟨root, rootEquation, rootCongruent⟩ :=
    HenselianRing.is_henselian polynomial polynomialMonic
      (PowerSeries.C constantRoot) rootMem quotientDerivativeUnit
  refine ⟨root, rootEquation, ?_⟩
  have constantDifference : PowerSeries.constantCoeff
      (root - PowerSeries.C constantRoot) = 0 := by
    rw [← PowerSeries.X_dvd_iff, ← Ideal.mem_span_singleton]
    exact rootCongruent
  rw [map_sub, PowerSeries.constantCoeff_C] at constantDifference
  exact sub_eq_zero.mp constantDifference

/-- Monicity is only a normalization issue when the leading coefficient is a
unit.  The result returns a root of the original polynomial, so later users
cannot accidentally stop at the normalized auxiliary equation. -/
theorem exists_powerSeries_root_of_unitLeading_simple_constant_root
    {L : Type*} [Field L]
    (polynomial : Polynomial (PowerSeries L))
    (leadingCoefficientUnit : IsUnit polynomial.leadingCoeff)
    (constantRoot : L)
    (rootModuloVariable : PowerSeries.constantCoeff
      (polynomial.eval (PowerSeries.C constantRoot)) = 0)
    (derivativeModuloVariableNeZero : PowerSeries.constantCoeff
      (polynomial.derivative.eval (PowerSeries.C constantRoot)) ≠ 0) :
    ∃ root : PowerSeries L,
      polynomial.IsRoot root ∧
        PowerSeries.constantCoeff root = constantRoot := by
  let normalized : Polynomial (PowerSeries L) :=
    leadingCoefficientUnit.unit⁻¹ • polynomial
  have normalizedMonic : normalized.Monic := by
    exact Polynomial.monic_of_isUnit_leadingCoeff_inv_smul
      leadingCoefficientUnit
  have inverseValueNeZero :
      ((leadingCoefficientUnit.unit⁻¹ : (PowerSeries L)ˣ) :
        PowerSeries L) ≠ 0 := Units.ne_zero _
  have normalizedRootModulo : PowerSeries.constantCoeff
      (normalized.eval (PowerSeries.C constantRoot)) = 0 := by
    dsimp only [normalized]
    rw [Polynomial.eval_smul]
    change PowerSeries.constantCoeff
      (((leadingCoefficientUnit.unit⁻¹ : (PowerSeries L)ˣ) :
        PowerSeries L) * polynomial.eval (PowerSeries.C constantRoot)) = 0
    rw [map_mul, rootModuloVariable, mul_zero]
  have normalizedDerivativeModulo : PowerSeries.constantCoeff
      (normalized.derivative.eval (PowerSeries.C constantRoot)) ≠ 0 := by
    dsimp only [normalized]
    rw [Polynomial.derivative_smul, Polynomial.eval_smul]
    change PowerSeries.constantCoeff
      (((leadingCoefficientUnit.unit⁻¹ : (PowerSeries L)ˣ) :
          PowerSeries L) *
        polynomial.derivative.eval (PowerSeries.C constantRoot)) ≠ 0
    rw [map_mul]
    exact mul_ne_zero
      (PowerSeries.isUnit_constantCoeff _
        (Units.isUnit leadingCoefficientUnit.unit⁻¹)).ne_zero
      derivativeModuloVariableNeZero
  obtain ⟨root, normalizedRoot, constantCoefficient⟩ :=
    exists_powerSeries_root_of_monic_simple_constant_root normalized
      normalizedMonic constantRoot normalizedRootModulo
      normalizedDerivativeModulo
  refine ⟨root, ?_, constantCoefficient⟩
  have evaluated :
      ((leadingCoefficientUnit.unit⁻¹ : (PowerSeries L)ˣ) :
          PowerSeries L) * polynomial.eval root = 0 := by
    rw [Polynomial.IsRoot] at normalizedRoot
    dsimp only [normalized] at normalizedRoot
    rw [Polynomial.eval_smul] at normalizedRoot
    change
      ((leadingCoefficientUnit.unit⁻¹ : (PowerSeries L)ˣ) :
          PowerSeries L) * polynomial.eval root = 0 at normalizedRoot
    exact normalizedRoot
  exact (mul_eq_zero.mp evaluated).resolve_left inverseValueNeZero

#print axioms exists_powerSeries_root_of_monic_simple_constant_root
#print axioms exists_powerSeries_root_of_unitLeading_simple_constant_root
#print axioms exists_adic_root_of_simple_approximation
#print axioms exists_powerSeries_root_of_simple_constant_root
#print axioms powerSeries_root_unique_of_simple_constant_root

end

end AspisK1.V7ExactCorrelatedAgreementHensel
