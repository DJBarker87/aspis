import AspisFormal.K1.V7Tag73ExactMultiplicityThreeGS

/-!
# Trivariate multiplicity-three interpolation for exact V7 curves

This is the base-field interpolation step of BCH+25 Lemma 3.1, specialized to
the two V7 parameter sets.  `X` is the Reed--Solomon evaluation variable,
`Y` is the candidate-polynomial variable, and the third exponent is the
batching challenge variable `Z`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7ExactCorrelatedAgreementInterpolation

open scoped BigOperators
open Polynomial
open AspisK1.V7Tag73ExactMultiplicityThreeGS

noncomputable section

/-- Monomial indices `X^i Y^j Z^h` satisfying the two strict weighted bounds
`i + maximumDegree*j < xBound` and
`h + curveDegree*j < zBound`. -/
abbrev CurveMonomialIndex
    (maximumDegree curveDegree xBound yRows zBound : Nat) :=
  Σ j : Fin yRows,
    Fin (xBound - maximumDegree * j.1) ×
      Fin (zBound - curveDegree * j.1)

/-- Reassociate a weighted bivariate monomial and one bounded `Z` exponent
as a trivariate curve monomial.  The strict `X` bound `D + 1` is exactly the
non-strict bivariate weighted-degree bound `D`. -/
def weightedCurveIndexEquiv
    (maximumDegree curveDegree weightedDegree ell zBound : Nat)
    (lastRow : maximumDegree * ell ≤ weightedDegree) :
    (Σ monomial :
        WeightedMonomialIndex maximumDegree weightedDegree ell,
      Fin (zBound - curveDegree * monomial.1.1)) ≃
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound where
  toFun monomial := by
    have rowBound : maximumDegree * monomial.1.1.1 ≤ weightedDegree := by
      have row : monomial.1.1.1 ≤ ell :=
        Nat.le_of_lt_succ monomial.1.1.2
      exact (Nat.mul_le_mul_left maximumDegree row).trans lastRow
    have sizeEquality :
        weightedDegree - maximumDegree * monomial.1.1.1 + 1 =
          weightedDegree + 1 - maximumDegree * monomial.1.1.1 := by
      omega
    exact ⟨monomial.1.1,
      ⟨Fin.cast sizeEquality monomial.1.2, monomial.2⟩⟩
  invFun monomial := by
    have rowBound : maximumDegree * monomial.1.1 ≤ weightedDegree := by
      have row : monomial.1.1 ≤ ell :=
        Nat.le_of_lt_succ monomial.1.2
      exact (Nat.mul_le_mul_left maximumDegree row).trans lastRow
    have sizeEquality :
        weightedDegree + 1 - maximumDegree * monomial.1.1 =
          weightedDegree - maximumDegree * monomial.1.1 + 1 := by
      omega
    exact ⟨⟨monomial.1, Fin.cast sizeEquality monomial.2.1⟩,
      monomial.2.2⟩
  left_inv monomial := by
    rcases monomial with ⟨⟨row, xExponent⟩, zExponent⟩
    rfl
  right_inv monomial := by
    rcases monomial with ⟨row, xExponent, zExponent⟩
    rfl

@[simp] theorem weightedCurveIndexEquiv_row
    (maximumDegree curveDegree weightedDegree ell zBound : Nat)
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (monomial : WeightedMonomialIndex maximumDegree weightedDegree ell)
    (zExponent : Fin (zBound - curveDegree * monomial.1.1)) :
    (weightedCurveIndexEquiv maximumDegree curveDegree weightedDegree ell
      zBound lastRow ⟨monomial, zExponent⟩).1 = monomial.1 := rfl

@[simp] theorem weightedCurveIndexEquiv_xExponent
    (maximumDegree curveDegree weightedDegree ell zBound : Nat)
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (monomial : WeightedMonomialIndex maximumDegree weightedDegree ell)
    (zExponent : Fin (zBound - curveDegree * monomial.1.1)) :
    (weightedCurveIndexEquiv maximumDegree curveDegree weightedDegree ell
      zBound lastRow ⟨monomial, zExponent⟩).2.1.1 = monomial.2.1 := rfl

@[simp] theorem weightedCurveIndexEquiv_zExponent
    (maximumDegree curveDegree weightedDegree ell zBound : Nat)
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (monomial : WeightedMonomialIndex maximumDegree weightedDegree ell)
    (zExponent : Fin (zBound - curveDegree * monomial.1.1)) :
    (weightedCurveIndexEquiv maximumDegree curveDegree weightedDegree ell
      zBound lastRow ⟨monomial, zExponent⟩).2.2 = zExponent := rfl

/-- For a fixed bivariate monomial `X^i Y^j`, collect its trivariate
coefficients into the corresponding polynomial in `Z`. -/
def curveCoefficientPolynomial
    {K : Type*} [Field K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (monomial : WeightedMonomialIndex maximumDegree weightedDegree ell) :
    K[X] :=
  AspisV5FriConcreteEncoderApplicability.monomialPolynomial fun zExponent =>
    coefficients (weightedCurveIndexEquiv maximumDegree curveDegree
      weightedDegree ell zBound lastRow ⟨monomial, zExponent⟩)

/-- Specialize the symbolic trivariate interpolant at one challenge. -/
def specializeCurveCoefficients
    {K : Type*} [Field K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (z : K) :
    WeightedMonomialIndex maximumDegree weightedDegree ell → K :=
  fun monomial =>
    (curveCoefficientPolynomial lastRow coefficients monomial).eval z

@[simp] theorem specializeCurveCoefficients_apply
    {K : Type*} [Field K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (z : K)
    (monomial : WeightedMonomialIndex maximumDegree weightedDegree ell) :
    specializeCurveCoefficients lastRow coefficients z monomial =
      ∑ zExponent,
        coefficients (weightedCurveIndexEquiv maximumDegree curveDegree
          weightedDegree ell zBound lastRow ⟨monomial, zExponent⟩) *
          z ^ zExponent.1 := by
  simp [specializeCurveCoefficients, curveCoefficientPolynomial,
    AspisV5FriConcreteEncoderApplicability.monomialPolynomial,
    Polynomial.eval_finsetSum]

/-- A nonzero trivariate coefficient vector has a nonzero `Z`-coefficient
polynomial in at least one bivariate row. -/
theorem exists_curveCoefficientPolynomial_ne_zero
    {K : Type*} [Field K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (coefficientsNeZero : coefficients ≠ 0) :
    ∃ monomial : WeightedMonomialIndex maximumDegree weightedDegree ell,
      curveCoefficientPolynomial lastRow coefficients monomial ≠ 0 := by
  classical
  have existsCoefficient : ∃ curveMonomial, coefficients curveMonomial ≠ 0 := by
    by_contra none
    push Not at none
    exact coefficientsNeZero (funext none)
  obtain ⟨curveMonomial, coefficientNeZero⟩ := existsCoefficient
  let indexed := (weightedCurveIndexEquiv maximumDegree curveDegree
    weightedDegree ell zBound lastRow).symm curveMonomial
  refine ⟨indexed.1, ?_⟩
  intro polynomialZero
  have coefficientZero := congrArg
    (fun polynomial : K[X] => polynomial.coeff indexed.2.1) polynomialZero
  have reindexed :
      weightedCurveIndexEquiv maximumDegree curveDegree weightedDegree ell
        zBound lastRow indexed = curveMonomial := by
    exact (weightedCurveIndexEquiv maximumDegree curveDegree weightedDegree ell
      zBound lastRow).apply_symm_apply curveMonomial
  simp only [curveCoefficientPolynomial,
    AspisV5FriConcreteEncoderApplicability.monomialPolynomial_coeff,
    Polynomial.coeff_zero] at coefficientZero
  rw [reindexed] at coefficientZero
  exact coefficientNeZero coefficientZero

def curveMonomialCount
    (maximumDegree curveDegree xBound yRows zBound : Nat) : Nat :=
  (Finset.range yRows).sum fun j =>
    (xBound - maximumDegree * j) * (zBound - curveDegree * j)

theorem curveMonomialIndex_card
    (maximumDegree curveDegree xBound yRows zBound : Nat) :
    Fintype.card
        (CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound) =
      curveMonomialCount maximumDegree curveDegree xBound yRows zBound := by
  simp only [CurveMonomialIndex, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin]
  rw [curveMonomialCount, ← Fin.sum_univ_eq_sum_range]

/-- The challenge polynomial of one coordinate of a degree-`curveDegree`
received-word curve. -/
def receivedCurvePolynomial
    {K : Type*} [Field K] {n curveDegree : Nat}
    (lanes : Fin (curveDegree + 1) → Fin n → K) (index : Fin n) : K[X] :=
  AspisV5FriConcreteEncoderApplicability.monomialPolynomial
    (fun lane => lanes lane index)

@[simp] theorem receivedCurvePolynomial_eval
    {K : Type*} [Field K] {n curveDegree : Nat}
    (lanes : Fin (curveDegree + 1) → Fin n → K) (index : Fin n) (z : K) :
    (receivedCurvePolynomial lanes index).eval z =
      ∑ lane, lanes lane index * z ^ lane.1 := by
  simp [receivedCurvePolynomial,
    AspisV5FriConcreteEncoderApplicability.monomialPolynomial,
    Polynomial.eval_finsetSum]

theorem receivedCurvePolynomial_natDegree_le
    {K : Type*} [Field K] {n curveDegree : Nat}
    (lanes : Fin (curveDegree + 1) → Fin n → K) (index : Fin n) :
    (receivedCurvePolynomial lanes index).natDegree ≤ curveDegree := by
  exact AspisV5FriConcreteEncoderApplicability.monomialPolynomial_natDegree_le
    (Nat.zero_lt_succ curveDegree) _

/-- One Hasse-constraint polynomial in `Z`.  Requiring all of its
coefficients to vanish is exactly the symbolic multiplicity-three condition
at a fixed RS evaluation point. -/
def curveConstraintPolynomial
    {K : Type*} [Field K]
    {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (points : Fin n → K)
    (lanes : Fin (curveDegree + 1) → Fin n → K)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (index : Fin n) (constraint : Fin 6) : K[X] :=
  ∑ monomial,
    C (coefficients monomial *
        (monomial.2.1.1.choose (hasseXOrder constraint) : K) *
        points index ^ (monomial.2.1.1 - hasseXOrder constraint) *
        (monomial.1.1.choose (hasseYOrder constraint) : K)) *
      (receivedCurvePolynomial lanes index ^
          (monomial.1.1 - hasseYOrder constraint) *
        X ^ monomial.2.2.1)

/-- Specializing the symbolic trivariate Hasse condition at `z` is exactly
the ordinary bivariate multiplicity-three constraint for the received word at
that challenge. -/
theorem interpolationConstraint_specializeCurveCoefficients
    {K : Type*} [Field K]
    {n maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (points : Fin n → K)
    (lanes : Fin (curveDegree + 1) → Fin n → K)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (index : Fin n) (constraint : Fin 6) (z : K) :
    interpolationConstraint (points index)
        ((receivedCurvePolynomial lanes index).eval z) constraint
        (specializeCurveCoefficients lastRow coefficients z) =
      (curveConstraintPolynomial points lanes coefficients index constraint).eval z := by
  classical
  rw [interpolationConstraint_apply]
  simp only [specializeCurveCoefficients_apply]
  unfold curveConstraintPolynomial
  rw [Polynomial.eval_finsetSum]
  rw [← (weightedCurveIndexEquiv maximumDegree curveDegree weightedDegree ell
    zBound lastRow).sum_comp]
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro xExponent _
  let monomial : WeightedMonomialIndex maximumDegree weightedDegree ell :=
    ⟨row, xExponent⟩
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro zExponent _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, weightedCurveIndexEquiv_row,
    weightedCurveIndexEquiv_xExponent, weightedCurveIndexEquiv_zExponent]
  ring

/-- Challenges at which every bivariate coefficient of the specialized
interpolant vanishes. -/
noncomputable def zeroCurveSpecializations
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K) : Finset K := by
  classical
  exact Finset.univ.filter fun z =>
    specializeCurveCoefficients lastRow coefficients z = 0

@[simp] theorem mem_zeroCurveSpecializations_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (z : K) :
    z ∈ zeroCurveSpecializations lastRow coefficients ↔
      specializeCurveCoefficients lastRow coefficients z = 0 := by
  classical
  simp [zeroCurveSpecializations]

/-- A nonzero symbolic interpolant has fewer than `zBound` zero
specializations.  This is the first exceptional-challenge term in the
published curve-decoding count. -/
theorem zeroCurveSpecializations_card_lt
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (coefficientsNeZero : coefficients ≠ 0) :
    (zeroCurveSpecializations lastRow coefficients).card < zBound := by
  classical
  obtain ⟨monomial, polynomialNeZero⟩ :=
    exists_curveCoefficientPolynomial_ne_zero lastRow coefficients
      coefficientsNeZero
  let polynomial := curveCoefficientPolynomial lastRow coefficients monomial
  have rowPositive : 0 < zBound - curveDegree * monomial.1.1 := by
    by_contra notPositive
    have rowZero : zBound - curveDegree * monomial.1.1 = 0 := by omega
    apply polynomialNeZero
    unfold curveCoefficientPolynomial
    have coefficientsZero :
        (fun zExponent : Fin (zBound - curveDegree * monomial.1.1) =>
          coefficients (weightedCurveIndexEquiv maximumDegree curveDegree
            weightedDegree ell zBound lastRow ⟨monomial, zExponent⟩)) = 0 := by
      funext zExponent
      exact Fin.elim0 (rowZero ▸ zExponent)
    rw [coefficientsZero]
    simp [AspisV5FriConcreteEncoderApplicability.monomialPolynomial]
  have rootsContain :
      (zeroCurveSpecializations lastRow coefficients).val ⊆
        polynomial.roots := by
    intro z zMem
    rw [Polynomial.mem_roots polynomialNeZero]
    have specializationZero :=
      (mem_zeroCurveSpecializations_iff lastRow coefficients z).mp zMem
    have coordinateZero := congrFun specializationZero monomial
    simpa [polynomial, specializeCurveCoefficients] using coordinateZero
  calc
    (zeroCurveSpecializations lastRow coefficients).card ≤
        polynomial.natDegree :=
      Polynomial.card_le_degree_of_subset_roots rootsContain
    _ ≤ zBound - curveDegree * monomial.1.1 - 1 := by
      exact AspisV5FriConcreteEncoderApplicability.monomialPolynomial_natDegree_le
        rowPositive _
    _ < zBound := by omega

/-- All bounded `Z`-coefficients of every symbolic Hasse condition, as one
finite-dimensional linear system over the base field. -/
def curveInterpolationMap
    {K : Type*} [Field K]
    {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (points : Fin n → K)
    (lanes : Fin (curveDegree + 1) → Fin n → K) :
    (CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) →ₗ[K]
      (Fin n → Fin 6 → Fin zBound → K) where
  toFun coefficients index constraint zCoefficient :=
    ∑ monomial,
      coefficients monomial *
        ((monomial.2.1.1.choose (hasseXOrder constraint) : K) *
          points index ^ (monomial.2.1.1 - hasseXOrder constraint) *
          (monomial.1.1.choose (hasseYOrder constraint) : K)) *
        (receivedCurvePolynomial lanes index ^
            (monomial.1.1 - hasseYOrder constraint) *
          X ^ monomial.2.2.1).coeff zCoefficient.1
  map_add' left right := by
    funext index constraint zCoefficient
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    funext index constraint zCoefficient
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro monomial _
    ring

theorem curveConstraintPolynomial_coeff
    {K : Type*} [Field K]
    {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (points : Fin n → K)
    (lanes : Fin (curveDegree + 1) → Fin n → K)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (index : Fin n) (constraint : Fin 6) (zCoefficient : Fin zBound) :
    (curveConstraintPolynomial points lanes coefficients index constraint).coeff
        zCoefficient.1 =
      curveInterpolationMap points lanes coefficients index constraint
        zCoefficient := by
  classical
  change (Polynomial.lcoeff K zCoefficient.1)
      (∑ monomial,
        C (coefficients monomial *
            (monomial.2.1.1.choose (hasseXOrder constraint) : K) *
            points index ^ (monomial.2.1.1 - hasseXOrder constraint) *
            (monomial.1.1.choose (hasseYOrder constraint) : K)) *
          (receivedCurvePolynomial lanes index ^
              (monomial.1.1 - hasseYOrder constraint) *
            X ^ monomial.2.2.1)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, curveInterpolationMap]
  apply Finset.sum_congr rfl
  intro monomial _
  rw [Polynomial.coeff_C_mul]
  ring

theorem curveConstraintPolynomial_natDegree_lt
    {K : Type*} [Field K]
    {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (zPositive : 0 < zBound)
    (points : Fin n → K)
    (lanes : Fin (curveDegree + 1) → Fin n → K)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (index : Fin n) (constraint : Fin 6) :
    (curveConstraintPolynomial points lanes coefficients index constraint).natDegree <
      zBound := by
  classical
  unfold curveConstraintPolynomial
  refine lt_of_le_of_lt (b := zBound - 1) ?_ (by omega)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro monomial _
  have receivedDegree := receivedCurvePolynomial_natDegree_le lanes index
  have receivedPowerDegree :
      (receivedCurvePolynomial lanes index ^
          (monomial.1.1 - hasseYOrder constraint)).natDegree ≤
        (monomial.1.1 - hasseYOrder constraint) * curveDegree := by
    exact Polynomial.natDegree_pow_le.trans
      (Nat.mul_le_mul_left _ receivedDegree)
  have zPowerDegree :
      (X ^ monomial.2.2.1 : K[X]).natDegree ≤ monomial.2.2.1 := by
    simp
  have productDegree :
      (receivedCurvePolynomial lanes index ^
          (monomial.1.1 - hasseYOrder constraint) *
        X ^ monomial.2.2.1).natDegree ≤
      (receivedCurvePolynomial lanes index ^
          (monomial.1.1 - hasseYOrder constraint)).natDegree +
        (X ^ monomial.2.2.1 : K[X]).natDegree :=
    Polynomial.natDegree_mul_le
  have weightedStrict :
      curveDegree * monomial.1.1 + monomial.2.2.1 < zBound := by
    have column := monomial.2.2.2
    omega
  have exponentWeight :
      (monomial.1.1 - hasseYOrder constraint) * curveDegree ≤
        curveDegree * monomial.1.1 := by
    calc
      (monomial.1.1 - hasseYOrder constraint) * curveDegree ≤
          monomial.1.1 * curveDegree :=
        Nat.mul_le_mul_right curveDegree (Nat.sub_le _ _)
      _ = curveDegree * monomial.1.1 := Nat.mul_comm _ _
  calc
    (C (coefficients monomial *
          (monomial.2.1.1.choose (hasseXOrder constraint) : K) *
          points index ^ (monomial.2.1.1 - hasseXOrder constraint) *
          (monomial.1.1.choose (hasseYOrder constraint) : K)) *
        (receivedCurvePolynomial lanes index ^
            (monomial.1.1 - hasseYOrder constraint) *
          X ^ monomial.2.2.1)).natDegree
        ≤ (receivedCurvePolynomial lanes index ^
              (monomial.1.1 - hasseYOrder constraint) *
            X ^ monomial.2.2.1).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
    _ ≤ ((monomial.1.1 - hasseYOrder constraint) * curveDegree) +
          monomial.2.2.1 := by
      simpa using productDegree.trans
        (Nat.add_le_add receivedPowerDegree zPowerDegree)
    _ ≤ curveDegree * monomial.1.1 + monomial.2.2.1 := by
      exact Nat.add_le_add_right exponentWeight _
    _ ≤ zBound - 1 := by omega

/-- A kernel vector makes the full symbolic Hasse condition vanish as a
polynomial in the batching challenge, not merely at one challenge. -/
theorem curveConstraintPolynomial_eq_zero_of_mem_kernel
    {K : Type*} [Field K]
    {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (zPositive : 0 < zBound)
    (points : Fin n → K)
    (lanes : Fin (curveDegree + 1) → Fin n → K)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (kernel : curveInterpolationMap points lanes coefficients = 0)
    (index : Fin n) (constraint : Fin 6) :
    curveConstraintPolynomial points lanes coefficients index constraint = 0 := by
  ext degree
  by_cases bounded : degree < zBound
  · let zCoefficient : Fin zBound := ⟨degree, bounded⟩
    rw [show degree = zCoefficient.1 by rfl,
      curveConstraintPolynomial_coeff]
    have pointwise := congrFun (congrFun (congrFun kernel index) constraint)
      zCoefficient
    simpa [curveInterpolationMap] using pointwise
  · have degreeBound := curveConstraintPolynomial_natDegree_lt zPositive
      points lanes coefficients index constraint
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le degreeBound (Nat.le_of_not_gt bounded))]
    simp

/-- Every specialization of a symbolic kernel vector satisfies the ordinary
multiplicity-three interpolation system for that challenge's received word.
The specialized vector may be zero at exceptional challenges; those
exceptions are bounded separately. -/
theorem specializeCurveCoefficients_mem_kernel
    {K : Type*} [Field K]
    {n maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (zPositive : 0 < zBound)
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (points : Fin n → K)
    (lanes : Fin (curveDegree + 1) → Fin n → K)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (kernel : curveInterpolationMap points lanes coefficients = 0)
    (z : K) :
    interpolationMap points
        (fun index => (receivedCurvePolynomial lanes index).eval z)
        (specializeCurveCoefficients lastRow coefficients z) = 0 := by
  funext index constraint
  change interpolationConstraint (points index)
      ((receivedCurvePolynomial lanes index).eval z) constraint
      (specializeCurveCoefficients lastRow coefficients z) = 0
  rw [interpolationConstraint_specializeCurveCoefficients]
  rw [curveConstraintPolynomial_eq_zero_of_mem_kernel zPositive points lanes
    coefficients kernel index constraint]
  simp

/-- Finite-dimensional kernel existence for the trivariate interpolation
system.  The codomain deliberately allocates `zBound` slots to every one of
the six Hasse constraints; this is a harmless over-count that simplifies the
formal dimension argument. -/
theorem exists_nonzero_curveInterpolationKernel
    {K : Type*} [Field K]
    {n maximumDegree curveDegree xBound yRows zBound : Nat}
    (points : Fin n → K)
    (lanes : Fin (curveDegree + 1) → Fin n → K)
    (dimension : 6 * n * zBound <
      curveMonomialCount maximumDegree curveDegree xBound yRows zBound) :
    ∃ coefficients :
        CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K,
      coefficients ≠ 0 ∧ curveInterpolationMap points lanes coefficients = 0 := by
  let constraints := curveInterpolationMap
    (maximumDegree := maximumDegree) (xBound := xBound) (yRows := yRows)
    (zBound := zBound) points lanes
  have finrank_lt :
      Module.finrank K (Fin n → Fin 6 → Fin zBound → K) <
        Module.finrank K
          (CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) := by
    have codomainRank :
        Module.finrank K (Fin n → Fin 6 → Fin zBound → K) =
          n * 6 * zBound := by
      simp only [Module.finrank_pi_fintype, Finset.sum_const, nsmul_eq_mul,
        Fintype.card_fin, Finset.card_univ,
        Module.finrank_self]
      norm_cast
      ring
    have domainRank :
        Module.finrank K
            (CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K) =
          curveMonomialCount maximumDegree curveDegree xBound yRows zBound := by
      rw [Module.finrank_pi, curveMonomialIndex_card]
    rw [codomainRank, domainRank]
    simpa [mul_assoc, mul_comm, mul_left_comm] using dimension
  have kernel_ne_bottom : LinearMap.ker constraints ≠ ⊥ :=
    constraints.ker_ne_bot_of_finrank_lt finrank_lt
  rw [Submodule.ne_bot_iff] at kernel_ne_bottom
  obtain ⟨coefficients, coefficients_mem, coefficients_ne_zero⟩ :=
    kernel_ne_bottom
  exact ⟨coefficients, coefficients_ne_zero,
    LinearMap.mem_ker.mp coefficients_mem⟩

/-! ## Exact V7 budgets -/

def initialCurveXBound : Nat := 114688
def initialCurveYRows : Nat := 112
def initialCurveZBound : Nat := 117078

def finalCurveXBound : Nat := 28674
def finalCurveYRows : Nat := 113
def finalCurveZBound : Nat := 12594

theorem exactInitialCurveInterpolationBudget :
    curveMonomialCount 1024 28 initialCurveXBound initialCurveYRows
        initialCurveZBound = 751937306624 ∧
      6 * 1048576 * initialCurveZBound = 736591085568 ∧
      6 * 1048576 * initialCurveZBound <
        curveMonomialCount 1024 28 initialCurveXBound initialCurveYRows
          initialCurveZBound := by
  norm_num [curveMonomialCount, initialCurveXBound, initialCurveYRows,
    initialCurveZBound, Finset.sum_range_succ]

theorem exactFinalCurveInterpolationBudget :
    curveMonomialCount 255 3 finalCurveXBound finalCurveYRows
        finalCurveZBound = 20303139852 ∧
      6 * 262144 * finalCurveZBound = 19808649216 ∧
      6 * 262144 * finalCurveZBound <
        curveMonomialCount 255 3 finalCurveXBound finalCurveYRows
          finalCurveZBound := by
  norm_num [curveMonomialCount, finalCurveXBound, finalCurveYRows,
    finalCurveZBound, Finset.sum_range_succ]

#print axioms curveConstraintPolynomial_eq_zero_of_mem_kernel
#print axioms interpolationConstraint_specializeCurveCoefficients
#print axioms exists_curveCoefficientPolynomial_ne_zero
#print axioms zeroCurveSpecializations_card_lt
#print axioms specializeCurveCoefficients_mem_kernel
#print axioms exists_nonzero_curveInterpolationKernel
#print axioms exactInitialCurveInterpolationBudget
#print axioms exactFinalCurveInterpolationBudget

end

end AspisK1.V7ExactCorrelatedAgreementInterpolation
