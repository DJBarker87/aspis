import AspisFormal.CircleNaturalBasis

/-!
# Exact sparse multiply-by-X map used by the v5 Good gate

The verifier stores degree-`<48` polynomials in the deployed natural line
basis.  Its `natural_mul_x` routine never materialises the dense conjugated
matrix: even source indices move to the next basis index, while odd source
indices propagate a trailing-one carry with successive factors of `1/2`.

This leaf models that exact width-48 recurrence and proves it is multiplication
by `X`, hence agrees with dense ordinary-to-natural conversion.  It also proves
the complete shift chain `0..11` used by GoodA (and therefore `0..3` used by
GoodB).  Coordinate 47 is intentionally excluded from the sparse source loop,
matching the Rust debug assertion; every theorem proves the required degree
bound rather than assuming silent truncation.
-/

namespace AspisV5GoodGateSparseShift

open Matrix Polynomial Polynomial.Chebyshev
open AspisCircleTensorBinding

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-! ## Literal sparse recurrence -/

/-- Number of consecutive low one-bits.  This is the mathematical graph of
Rust's `usize::trailing_ones()` on the reachable indices `0..46`. -/
def trailingOnes : Nat → Nat
  | n => if n % 2 = 0 then 0 else 1 + trailingOnes (n / 2)
termination_by n => n
decreasing_by
  apply Nat.div_lt_self <;> omega

/-- The coefficient obtained after `count` calls to `M31::half()`. -/
def dyadic (count : Nat) : K := ((2 : K) ^ count)⁻¹

/-- Embed source indices `0..46` in the width-48 vector. -/
def sourceIndex (index : Fin 47) : Fin 48 := index.castSucc

/-- The always-valid `index + 1` target. -/
def successorIndex (index : Fin 47) : Fin 48 := ⟨index + 1, by omega⟩

/-- The target written by carry number `carry`, literally
`index - ((1 << carry) - 1)` from Rust. -/
def carryIndex (index : Fin 47) (carry : Nat) : Fin 48 :=
  ⟨index - (2 ^ carry - 1), by omega⟩

/-- One source column of the exact sparse natural-basis shift. -/
def sparseBasis (index : Fin 47) : Fin 48 → K :=
  if (index : Nat) % 2 = 0 then
    Pi.single (successorIndex index) 1
  else
    let count := trailingOnes (index : Nat)
    Pi.single (successorIndex index) (dyadic count) +
      ∑ carry ∈ Finset.range count,
        Pi.single (carryIndex index (carry + 1)) (dyadic (carry + 1))

/-- Exact width-48 `natural_mul_x`: Rust loops over source indices `0..46`
and accumulates each sparse column into the output. -/
def sparseShift (input : Fin 48 → K) : Fin 48 → K :=
  Fintype.linearCombination K (sparseBasis (K := K))
    (fun index : Fin 47 => input (sourceIndex index))

/-- Dense ordinary multiplication by `X`, truncated to width 48. -/
def ordinaryShift (input : Fin 48 → K) : Fin 48 → K :=
  Fin.cons 0 (fun index : Fin 47 => input (sourceIndex index))

/-- Canonical ordinary-to-natural conversion at the deployed width. -/
noncomputable def convert (ordinary : Fin 48 → K) : Fin 48 → K :=
  (monomialToNatural K 48).mulVec ordinary

/-! ## Polynomial semantics of the natural basis -/

/-- Synthesis from width-48 natural coefficients, packaged as the canonical
finite linear-combination map.  Keeping the linear structure bundled avoids
re-elaborating the 48-term sum in every linearity lemma. -/
noncomputable def naturalSynthesisMap : (Fin 48 → K) →ₗ[K] K[X] :=
  Fintype.linearCombination K (fun index : Fin 48 => naturalLinePoly K index)

/-- Synthesis from width-48 natural coefficients. -/
noncomputable def naturalSynthesis (coefficients : Fin 48 → K) : K[X] :=
  naturalSynthesisMap coefficients

omit [NeZero (2 : K)] in
/-- Linear maps commute with finite linear combinations.  Keeping this fact
generic prevents Lean from duplicating a large column proof at all 47 indices. -/
theorem map_fintypeLinearCombination {I M N : Type*} [Fintype I]
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (map : M →ₗ[K] N) (vectors : I → M) (coefficients : I → K) :
    map (Fintype.linearCombination K vectors coefficients) =
      Fintype.linearCombination K (fun index => map (vectors index)) coefficients := by
  classical
  simp only [Fintype.linearCombination_apply, map_sum, map_smul]

omit [NeZero (2 : K)] in
/-- Pointwise-equal vector families have equal finite linear combinations. -/
theorem fintypeLinearCombination_congr {I M : Type*} [Fintype I]
    [AddCommMonoid M] [Module K M] (left right : I → M)
    (coefficients : I → K) (equal : ∀ index, left index = right index) :
    Fintype.linearCombination K left coefficients =
      Fintype.linearCombination K right coefficients := by
  classical
  simp only [Fintype.linearCombination_apply]
  apply Finset.sum_congr rfl
  intro index _
  rw [equal index]

omit [NeZero (2 : K)] in
@[simp] theorem naturalSynthesis_apply (coefficients : Fin 48 → K) :
    naturalSynthesis coefficients =
      ∑ index : Fin 48, C (coefficients index) * naturalLinePoly K index := by
  simp only [naturalSynthesis, naturalSynthesisMap,
    Fintype.linearCombination_apply, Polynomial.smul_eq_C_mul]

omit [NeZero (2 : K)] in
@[simp] theorem naturalSynthesis_single (index : Fin 48) (coefficient : K) :
    naturalSynthesis (Pi.single index coefficient) =
      C coefficient * naturalLinePoly K index := by
  classical
  change naturalSynthesisMap (Pi.single index coefficient) = _
  rw [naturalSynthesisMap, Fintype.linearCombination_apply_single,
    Polynomial.smul_eq_C_mul]

/-- Synthesis from ordinary monomial coefficients. -/
noncomputable def ordinarySynthesis (coefficients : Fin 48 → K) : K[X] :=
  ∑ degree : Fin 48, C (coefficients degree) * X ^ (degree : Nat)

omit [NeZero (2 : K)] in
theorem ordinarySynthesis_coeff (coefficients : Fin 48 → K) (degree : Nat) :
    (ordinarySynthesis coefficients).coeff degree =
      if h : degree < 48 then coefficients ⟨degree, h⟩ else 0 := by
  classical
  unfold ordinarySynthesis
  rw [← lcoeff_apply, map_sum]
  by_cases hdegree : degree < 48
  · simp only [hdegree, ↓reduceDIte]
    let d : Fin 48 := ⟨degree, hdegree⟩
    calc
      (∑ index : Fin 48, (C (coefficients index) * X ^ (index : Nat)).coeff degree) =
          (C (coefficients d) * X ^ (d : Nat)).coeff degree := by
        apply Fintype.sum_eq_single d
        intro other hne
        simp [coeff_C_mul, d, Fin.ext_iff] at hne ⊢
        omega
      _ = coefficients ⟨degree, hdegree⟩ := by simp [coeff_C_mul, d]
  · simp only [hdegree, ↓reduceDIte]
    apply Finset.sum_eq_zero
    intro index _
    simp [coeff_C_mul]
    omega

omit [NeZero (2 : K)] in
/-- Multiplying an ordinary coefficient vector by `X` agrees with polynomial
multiplication whenever degree 47 is zero. -/
theorem ordinarySynthesis_shift (ordinary : Fin 48 → K)
    (htop : ordinary (47 : Fin 48) = 0) :
    ordinarySynthesis (ordinaryShift ordinary) = X * ordinarySynthesis ordinary := by
  ext degree
  cases degree with
  | zero =>
      rw [ordinarySynthesis_coeff]
      simp [ordinaryShift]
  | succ degree =>
      rw [ordinarySynthesis_coeff, coeff_X_mul, ordinarySynthesis_coeff]
      by_cases hlt : degree < 47
      · have hsucc : degree + 1 < 48 := by omega
        have hdegree : degree < 48 := by omega
        simp only [hsucc, hdegree, dif_pos]
        let d : Fin 47 := ⟨degree, hlt⟩
        change ordinaryShift ordinary d.succ = ordinary (sourceIndex d)
        rfl
      · by_cases heq : degree = 47
        · subst degree
          simp [show 47 < 48 by omega]
          exact htop.symm
        · have hlarge : 48 ≤ degree := by omega
          simp [show ¬degree + 1 < 48 by omega, show ¬degree < 48 by omega]

/-! ## Natural-basis multiplication identities -/

omit [NeZero (2 : K)] in
/-- The power-of-two Chebyshev square identity used at every carry. -/
theorem chebyshev_bit_square (bit : Nat) :
    2 * T K (2 ^ bit : Nat) * T K (2 ^ bit : Nat) =
      T K (2 ^ (bit + 1) : Nat) + 1 := by
  rw [T_mul_T]
  congr 1
  · congr 2
    all_goals omega
  · norm_num

/-- Polynomial represented by one literal sparse source column. -/
noncomputable def sparseBasisPolynomial (index : Fin 47) : K[X] :=
  if (index : Nat) % 2 = 0 then
    naturalLinePoly K ((index : Nat) + 1)
  else
    let count := trailingOnes (index : Nat)
    C (dyadic count) * naturalLinePoly K ((index : Nat) + 1) +
      ∑ carry ∈ Finset.range count,
        C (dyadic (carry + 1)) *
          naturalLinePoly K ((index : Nat) - (2 ^ (carry + 1) - 1))

omit [NeZero (2 : K)] in
theorem naturalSynthesis_add (left right : Fin 48 → K) :
    naturalSynthesis (left + right) =
      naturalSynthesis left + naturalSynthesis right := by
  exact map_add naturalSynthesisMap left right

omit [NeZero (2 : K)] in
theorem naturalSynthesis_sum {n : Nat} (columns : Fin n → Fin 48 → K) :
    naturalSynthesis (∑ index, columns index) =
      ∑ index, naturalSynthesis (columns index) := by
  unfold naturalSynthesis
  rw [map_sum]

omit [NeZero (2 : K)] in
theorem naturalSynthesis_finset_sum {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (columns : ι → Fin 48 → K) :
    naturalSynthesis (∑ index ∈ indices, columns index) =
      ∑ index ∈ indices, naturalSynthesis (columns index) := by
  unfold naturalSynthesis
  rw [map_sum]

omit [NeZero (2 : K)] in
/-- Synthesis of a sparse column is its explicit small polynomial sum. -/
theorem naturalSynthesis_sparseBasis (index : Fin 47) :
    naturalSynthesis (sparseBasis (K := K) index) = sparseBasisPolynomial (K := K) index := by
  classical
  unfold sparseBasis sparseBasisPolynomial
  split
  · rw [naturalSynthesis_single]
    simp [successorIndex]
  · change naturalSynthesis
        (Pi.single (successorIndex index) (dyadic (trailingOnes (index : Nat))) +
          ∑ carry ∈ Finset.range (trailingOnes (index : Nat)),
            Pi.single (carryIndex index (carry + 1))
              (dyadic (carry + 1))) = _
    rw [naturalSynthesis_add, naturalSynthesis_finset_sum]
    simp only [naturalSynthesis_single]
    rfl

omit [NeZero (2 : K)] in
@[simp] theorem dyadic_zero : dyadic (K := K) 0 = 1 := by
  simp [dyadic]

omit [NeZero (2 : K)] in
@[simp] theorem dyadic_succ (count : Nat) :
    dyadic (K := K) (count + 1) =
      (2 : K)⁻¹ * dyadic (K := K) count := by
  simp [dyadic, pow_succ, _root_.mul_inv_rev, mul_comm]

omit [NeZero (2 : K)] in
theorem naturalLinePoly_even (index : Nat) :
    naturalLinePoly K (2 * index) =
      (naturalLinePoly K index).comp (T K 2) := by
  simp only [naturalLinePoly, Nat.bitIndices_two_mul]
  rw [Polynomial.prod_comp]
  rw [show (index.bitIndices.map (fun bit => bit + 1)).toFinset =
      index.bitIndices.toFinset.image (fun bit => bit + 1) by
        ext bit
        simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro bit hbit
    simpa [pow_succ, mul_comm] using (T_mul K (2 ^ bit : ℤ) 2)
  · intro left _ right _ equal
    exact Nat.add_right_cancel equal

omit [NeZero (2 : K)] in
theorem naturalLinePoly_odd (index : Nat) :
    naturalLinePoly K (2 * index + 1) =
      X * naturalLinePoly K (2 * index) := by
  rw [naturalLinePoly, Nat.bitIndices_two_mul_add_one,
    List.toFinset_cons, Finset.prod_insert]
  · rw [naturalLinePoly, Nat.bitIndices_two_mul]
    simp
  · simp

omit [NeZero (2 : K)] in
@[simp] theorem naturalLinePoly_comp_T_two (index : Nat) :
    (naturalLinePoly K index).comp (T K 2) =
      naturalLinePoly K (2 * index) :=
  (naturalLinePoly_even index).symm

/-- A recurrence with the exact same even/odd branches as Rust, but phrased
as polynomials so its correctness can be proved once by strong induction. -/
noncomputable def recursiveShiftPolynomial (index : Nat) : K[X] :=
  if hEven : index % 2 = 0 then
    naturalLinePoly K (index + 1)
  else
    C ((2 : K)⁻¹) * naturalLinePoly K (index - 1) +
      C ((2 : K)⁻¹) *
        (recursiveShiftPolynomial (index / 2)).comp (T K 2)
termination_by index
decreasing_by
  have hpositive : 0 < index := by
    by_contra hzero
    have : index = 0 := by omega
    subst index
    simp at hEven
  exact Nat.div_lt_self hpositive (by omega)

theorem recursiveShiftPolynomial_eq_mul_X (index : Nat) :
    recursiveShiftPolynomial (K := K) index =
      X * naturalLinePoly K index := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [recursiveShiftPolynomial]
      split
      case isTrue hEven =>
        have heven : Even index := Nat.even_iff.mpr hEven
        obtain ⟨halfIndex, rfl⟩ := even_iff_exists_two_mul.mp heven
        rw [naturalLinePoly_odd]
      case isFalse hOdd =>
        have hmod : index % 2 = 1 := by omega
        have hodd : Odd index := Nat.odd_iff.mpr hmod
        obtain ⟨halfIndex, rfl⟩ := Odd.exists_bit1 hodd
        have hdiv : (2 * halfIndex + 1) / 2 = halfIndex := by omega
        simp only [Nat.add_sub_cancel]
        rw [hdiv, ih halfIndex (by omega), mul_comp, X_comp,
          naturalLinePoly_odd, naturalLinePoly_even]
        rw [T_two]
        have hhalf : C ((2 : K)⁻¹) * (2 : K[X]) = 1 := by
          rw [← C_ofNat, ← Polynomial.C_mul,
            inv_mul_cancel₀ (NeZero.ne 2)]
          exact map_one (Polynomial.C : K →+* K[X])
        calc
          C ((2 : K)⁻¹) *
                (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1) +
              C ((2 : K)⁻¹) *
                ((2 * X ^ 2 - 1) *
                  (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1)) =
              (C ((2 : K)⁻¹) * (2 : K[X])) *
                (X ^ 2 *
                  (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1)) := by
            ring
          _ = X ^ 2 *
                (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1) := by
            rw [hhalf, one_mul]
          _ = X *
                (X * (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1)) := by
            simp only [pow_two, mul_assoc]

theorem trailingOnes_of_even (index : Nat) (hEven : index % 2 = 0) :
    trailingOnes index = 0 := by
  rw [trailingOnes, if_pos hEven]

theorem trailingOnes_of_odd (index : Nat) (hOdd : index % 2 ≠ 0) :
    trailingOnes index = 1 + trailingOnes (index / 2) := by
  rw [trailingOnes, if_neg hOdd]

@[simp] theorem trailingOnes_two_mul_add_one (index : Nat) :
    trailingOnes (2 * index + 1) = 1 + trailingOnes index := by
  rw [trailingOnes]
  have hmod : (2 * index + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  congr 1
  congr 1
  omega

theorem pow_trailingOnes_le_succ (index : Nat) :
    2 ^ trailingOnes index ≤ index + 1 := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      by_cases hEven : index % 2 = 0
      · rw [trailingOnes_of_even index hEven]
        simp
      · rw [trailingOnes_of_odd index hEven, pow_add, pow_one]
        have hpositive : 0 < index := by
          by_contra hzero
          have : index = 0 := by omega
          subst index
          simp at hEven
        have hhalf : index / 2 < index := Nat.div_lt_self hpositive (by omega)
        have hrec := ih (index / 2) hhalf
        have hmod : index % 2 = 1 := by omega
        omega

/-- Nat-indexed spelling of one sparse column; using `Finset.range` matches
the Rust `0..count` carry loop without dependent casts. -/
noncomputable def sparseFormula (index : Nat) : K[X] :=
  if index % 2 = 0 then
    naturalLinePoly K (index + 1)
  else
    let count := trailingOnes index
    C (dyadic count) * naturalLinePoly K (index + 1) +
      ∑ carry ∈ Finset.range count,
        C (dyadic (carry + 1)) *
          naturalLinePoly K (index - (2 ^ (carry + 1) - 1))

omit [NeZero (2 : K)] in
theorem sparseFormula_eq_carry_expansion (index : Nat) :
    sparseFormula (K := K) index =
      C (dyadic (K := K) (trailingOnes index)) *
          naturalLinePoly K (index + 1) +
        ∑ carry ∈ Finset.range (trailingOnes index),
          C (dyadic (K := K) (carry + 1)) *
            naturalLinePoly K (index - (2 ^ (carry + 1) - 1)) := by
  rw [sparseFormula]
  by_cases hEven : index % 2 = 0
  · rw [if_pos hEven, trailingOnes_of_even index hEven]
    simp
  · rw [if_neg hEven]

theorem carry_index_double (index carry : Nat)
    (hcarry : carry < trailingOnes index) :
    2 * index + 1 - (2 ^ (carry + 2) - 1) =
      2 * (index - (2 ^ (carry + 1) - 1)) := by
  have hpow : 2 ^ (carry + 1) ≤ 2 ^ trailingOnes index := by
    exact Nat.pow_le_pow_right (by omega) (Nat.succ_le_of_lt hcarry)
  have htop := pow_trailingOnes_le_succ index
  have hbound : 2 ^ (carry + 1) - 1 ≤ index := by omega
  have hcancel := Nat.sub_add_cancel hbound
  have hpositive : 0 < 2 ^ (carry + 1) := pow_pos (by omega) _
  have hdouble :
      2 ^ (carry + 2) - 1 =
        2 * (2 ^ (carry + 1) - 1) + 1 := by
    rw [show carry + 2 = (carry + 1) + 1 by omega, pow_succ]
    omega
  rw [hdouble]
  omega

omit [NeZero (2 : K)] in
theorem sparseFormula_odd_recurrence (index : Nat) :
    sparseFormula (K := K) (2 * index + 1) =
      C ((2 : K)⁻¹) * naturalLinePoly K (2 * index) +
        C ((2 : K)⁻¹) *
          (sparseFormula (K := K) index).comp (T K 2) := by
  rw [sparseFormula_eq_carry_expansion, sparseFormula_eq_carry_expansion]
  rw [trailingOnes_two_mul_add_one]
  simp only [Nat.one_add, Finset.sum_range_succ']
  have hmain :
      C (dyadic (K := K) (trailingOnes index).succ) *
          naturalLinePoly K (2 * index + 1 + 1) =
        C ((2 : K)⁻¹) *
          (C (dyadic (K := K) (trailingOnes index)) *
            naturalLinePoly K (index + 1)).comp (T K 2) := by
    rw [show (trailingOnes index).succ = trailingOnes index + 1 by omega,
      dyadic_succ, map_mul, mul_comp, C_comp]
    rw [show 2 * index + 1 + 1 = 2 * (index + 1) by omega,
      naturalLinePoly_even]
    ring
  have hfirst :
      C (dyadic (K := K) (0 + 1)) *
          naturalLinePoly K (2 * index + 1 - (2 ^ (0 + 1) - 1)) =
        C ((2 : K)⁻¹) * naturalLinePoly K (2 * index) := by
    simp [dyadic]
  have htail :
      (∑ carry ∈ Finset.range (trailingOnes index),
        C (dyadic (K := K) (carry + 1 + 1)) *
          naturalLinePoly K
            (2 * index + 1 - (2 ^ (carry + 1 + 1) - 1))) =
        C ((2 : K)⁻¹) *
          (∑ carry ∈ Finset.range (trailingOnes index),
            C (dyadic (K := K) (carry + 1)) *
              naturalLinePoly K
                (index - (2 ^ (carry + 1) - 1))).comp (T K 2) := by
    rw [Polynomial.sum_comp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro carry hcarry
    have hcarry' := Finset.mem_range.mp hcarry
    rw [mul_comp, C_comp, naturalLinePoly_comp_T_two]
    rw [show carry + 1 + 1 = (carry + 1) + 1 by omega,
      dyadic_succ, map_mul]
    rw [carry_index_double index carry hcarry']
    ring
  rw [hmain, hfirst, htail, add_comp]
  ring

omit [NeZero (2 : K)] in
theorem sparseFormula_eq_recursive (index : Nat) :
    sparseFormula (K := K) index =
      recursiveShiftPolynomial (K := K) index := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [recursiveShiftPolynomial]
      by_cases hEven : index % 2 = 0
      · rw [dif_pos hEven, sparseFormula, if_pos hEven]
      · rw [dif_neg hEven]
        have hpositive : 0 < index := by
          by_contra hzero
          have : index = 0 := by omega
          subst index
          simp at hEven
        have hhalf : index / 2 < index := Nat.div_lt_self hpositive (by omega)
        have hmod : index % 2 = 1 := by omega
        have hshape : index = 2 * (index / 2) + 1 := by omega
        have hsub : index - 1 = 2 * (index / 2) := by omega
        conv_lhs => rw [hshape, sparseFormula_odd_recurrence]
        rw [ih (index / 2) hhalf, hsub]

omit [NeZero (2 : K)] in
theorem sparseBasisPolynomial_eq_sparseFormula (index : Fin 47) :
    sparseBasisPolynomial (K := K) index =
      sparseFormula (K := K) index := by
  rfl

/-- Every reachable sparse column is exactly multiplication by `X` in the
natural line basis.  The proof is generic and recursive, not a 47-case KAT. -/
theorem sparseBasisPolynomial_eq_mul_X (index : Fin 47) :
    sparseBasisPolynomial (K := K) index =
      X * naturalLinePoly K index := by
  rw [sparseBasisPolynomial_eq_sparseFormula,
    sparseFormula_eq_recursive, recursiveShiftPolynomial_eq_mul_X]

/-- Polynomial semantics of the exact Rust sparse source column. -/
theorem naturalSynthesis_sparseBasis_eq_mul_X (index : Fin 47) :
    naturalSynthesis (sparseBasis (K := K) index) =
      X * naturalLinePoly K index := by
  rw [naturalSynthesis_sparseBasis, sparseBasisPolynomial_eq_mul_X]

/-! ## Conversion and one-step commuting square -/

omit [NeZero (2 : K)] in
/-- Coefficients of a synthesized natural polynomial are the deployed
natural coefficient matrix times the natural vector. -/
theorem naturalSynthesis_coeff (coefficients : Fin 48 → K) (degree : Fin 48) :
    (naturalSynthesis coefficients).coeff degree =
      (naturalCoeffMatrix K 48).mulVec coefficients degree := by
  rw [naturalSynthesis_apply, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, coeff_C_mul, Matrix.mulVec, dotProduct,
    naturalCoeffMatrix]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

/-- Natural synthesis is injective at width 48. -/
theorem naturalSynthesis_injective : Function.Injective (naturalSynthesis (K := K)) := by
  intro left right equal
  have hunit : IsUnit (naturalCoeffMatrix K 48) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (naturalCoeffMatrix_det_ne_zero (K := K) 48))
  apply Matrix.mulVec_injective_iff_isUnit.mpr hunit
  funext degree
  rw [← naturalSynthesis_coeff, ← naturalSynthesis_coeff, equal]

/-- Conversion synthesizes the same polynomial as the ordinary coefficient
vector. -/
theorem naturalSynthesis_convert (ordinary : Fin 48 → K) :
    naturalSynthesis (convert ordinary) = ordinarySynthesis ordinary := by
  ext degree
  by_cases hdegree : degree < 48
  · let d : Fin 48 := ⟨degree, hdegree⟩
    have hmatrix := congrFun
      (Matrix.mulVec_mulVec ordinary (naturalCoeffMatrix K 48)
        (monomialToNatural K 48)) d
    rw [naturalCoeff_mul_monomialToNatural, Matrix.one_mulVec] at hmatrix
    change (naturalSynthesis (convert ordinary)).coeff (d : Nat) =
      (ordinarySynthesis ordinary).coeff (d : Nat)
    rw [naturalSynthesis_coeff]
    rw [show convert ordinary = (monomialToNatural K 48).mulVec ordinary from rfl]
    rw [hmatrix, ordinarySynthesis_coeff]
    simp [d, hdegree]
  · have hlarge : 48 ≤ degree := by omega
    rw [naturalSynthesis_apply, ordinarySynthesis]
    simp only [← lcoeff_apply]
    rw [map_sum, map_sum]
    rw [Finset.sum_eq_zero (fun index _ => by
        rw [lcoeff_apply, coeff_C_mul, coeff_eq_zero_of_natDegree_lt]
        · simp
        · rw [naturalLinePoly_natDegree]
          omega),
      Finset.sum_eq_zero (fun index _ => by
        simp [lcoeff_apply, coeff_C_mul]
        omega)]

omit [NeZero (2 : K)] in
theorem naturalSynthesis_smul (scale : K) (coefficients : Fin 48 → K) :
    naturalSynthesis (scale • coefficients) =
      C scale * naturalSynthesis coefficients := by
  change naturalSynthesisMap (scale • coefficients) =
    C scale * naturalSynthesisMap coefficients
  rw [map_smul, Polynomial.smul_eq_C_mul]

/-- The canonical embedding of one retained source coordinate into width 48. -/
def prefixBasis (index : Fin 47) : Fin 48 → K :=
  Pi.single index.castSucc 1

/-- Width-47 coefficients embedded in width 48 with zero final coordinate. -/
def prefixEmbed (coefficients : Fin 47 → K) : Fin 48 → K :=
  Fintype.linearCombination K (prefixBasis (K := K)) coefficients

omit [NeZero (2 : K)] in
@[simp] theorem prefixEmbed_castSucc (coefficients : Fin 47 → K)
    (index : Fin 47) :
    prefixEmbed coefficients index.castSucc = coefficients index := by
  classical
  simp [prefixEmbed, prefixBasis, Fintype.linearCombination_apply,
    Pi.single_apply]

omit [NeZero (2 : K)] in
@[simp] theorem prefixEmbed_last (coefficients : Fin 47 → K) :
    prefixEmbed coefficients (Fin.last 47) = 0 := by
  classical
  rw [prefixEmbed, Fintype.linearCombination_apply]
  rw [Fintype.sum_apply]
  apply Finset.sum_eq_zero
  intro index _
  simp only [Pi.smul_apply, prefixBasis, Pi.single_apply]
  rw [if_neg (Fin.castSucc_ne_last index).symm, smul_zero]

omit [NeZero (2 : K)] in
/-- A width-48 vector with zero last coordinate is exactly its width-47 prefix
embedding; no sum decomposition at concrete arity is needed. -/
theorem prefixEmbed_source_eq (input : Fin 48 → K)
    (htop : input (47 : Fin 48) = 0) :
    prefixEmbed (fun index : Fin 47 => input (sourceIndex index)) = input := by
  funext coordinate
  refine Fin.lastCases ?_ (fun index => ?_) coordinate
  · rw [prefixEmbed_last]
    exact htop.symm
  · rw [prefixEmbed_castSucc]
    rfl

omit [NeZero (2 : K)] in
/-- Synthesis of the prefix embedding is the finite combination of the first
47 natural-basis polynomials. -/
theorem naturalSynthesis_prefixEmbed (coefficients : Fin 47 → K) :
    naturalSynthesis (prefixEmbed coefficients) =
      Fintype.linearCombination K
        (fun index : Fin 47 => naturalLinePoly K index) coefficients := by
  change naturalSynthesisMap
      (Fintype.linearCombination K (prefixBasis (K := K)) coefficients) = _
  calc
    naturalSynthesisMap
          (Fintype.linearCombination K (prefixBasis (K := K)) coefficients) =
        Fintype.linearCombination K
          (fun index : Fin 47 =>
            naturalSynthesisMap (prefixBasis (K := K) index)) coefficients :=
      map_fintypeLinearCombination naturalSynthesisMap
        (prefixBasis (K := K)) coefficients
    _ = Fintype.linearCombination K
          (fun index : Fin 47 => naturalLinePoly K index) coefficients :=
      fintypeLinearCombination_congr _ _ coefficients (fun index => by
        change naturalSynthesis (Pi.single index.castSucc 1) = _
        rw [naturalSynthesis_single]
        simp)

/-- Synthesis sends the finite combination of exact sparse Rust columns to
the corresponding finite combination of multiplication-by-`X` polynomials. -/
theorem naturalSynthesis_sparseCombination (coefficients : Fin 47 → K) :
    naturalSynthesisMap
        (Fintype.linearCombination K (sparseBasis (K := K)) coefficients) =
      Fintype.linearCombination K
        (fun index : Fin 47 => X * naturalLinePoly K index) coefficients := by
  calc
    naturalSynthesisMap
          (Fintype.linearCombination K (sparseBasis (K := K)) coefficients) =
        Fintype.linearCombination K
          (fun index : Fin 47 =>
            naturalSynthesisMap (sparseBasis (K := K) index)) coefficients :=
      map_fintypeLinearCombination naturalSynthesisMap
        (sparseBasis (K := K)) coefficients
    _ = Fintype.linearCombination K
          (fun index : Fin 47 => X * naturalLinePoly K index) coefficients :=
      fintypeLinearCombination_congr _ _ coefficients
        (fun index => naturalSynthesis_sparseBasis_eq_mul_X index)

omit [NeZero (2 : K)] in
/-- Left multiplication by `X` factors out of the exact width-47 finite
linear combination. -/
theorem mulX_fintypeLinearCombination (coefficients : Fin 47 → K) :
    Fintype.linearCombination K
        (fun index : Fin 47 => X * naturalLinePoly K index) coefficients =
      X * Fintype.linearCombination K
        (fun index : Fin 47 => naturalLinePoly K index) coefficients := by
  exact (map_fintypeLinearCombination (LinearMap.mulLeft K X)
    (fun index : Fin 47 => naturalLinePoly K index) coefficients).symm

/-- The exact sparse vector routine synthesizes multiplication by `X` when
the discarded source coordinate 47 is zero. -/
theorem naturalSynthesis_sparseShift (input : Fin 48 → K)
    (htop : input (47 : Fin 48) = 0) :
    naturalSynthesis (sparseShift input) =
      X * naturalSynthesis input := by
  let coefficients : Fin 47 → K := fun index => input (sourceIndex index)
  have hprefix : prefixEmbed coefficients = input :=
    prefixEmbed_source_eq input htop
  change naturalSynthesisMap
      (Fintype.linearCombination K (sparseBasis (K := K)) coefficients) = _
  calc
    naturalSynthesisMap
          (Fintype.linearCombination K (sparseBasis (K := K)) coefficients) =
        Fintype.linearCombination K
          (fun index : Fin 47 => X * naturalLinePoly K index) coefficients :=
      naturalSynthesis_sparseCombination coefficients
    _ = X * Fintype.linearCombination K
          (fun index : Fin 47 => naturalLinePoly K index) coefficients :=
      mulX_fintypeLinearCombination coefficients
    _ = X * naturalSynthesis (prefixEmbed coefficients) := by
      rw [naturalSynthesis_prefixEmbed]
    _ = X * naturalSynthesis input := by
      rw [hprefix]

/-- Coordinate 47 of natural synthesis is its natural coefficient times the
nonzero leading coefficient of basis element 47. -/
theorem naturalSynthesis_top_coeff (coefficients : Fin 48 → K) :
    (naturalSynthesis coefficients).coeff 47 =
      coefficients (47 : Fin 48) *
        (naturalLinePoly K 47).leadingCoeff := by
  classical
  rw [naturalSynthesis_apply, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply]
  calc
    (∑ index : Fin 48,
        (C (coefficients index) * naturalLinePoly K index).coeff 47) =
        (C (coefficients (47 : Fin 48)) *
          naturalLinePoly K (47 : Fin 48)).coeff 47 := by
      apply Fintype.sum_eq_single (47 : Fin 48)
      intro index hindex
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt]
      · simp
      · rw [naturalLinePoly_natDegree]
        have hlt := index.isLt
        have hne : (index : Nat) ≠ 47 := by
          intro equal
          apply hindex
          exact Fin.ext equal
        omega
    _ = coefficients (47 : Fin 48) *
          (naturalLinePoly K 47).leadingCoeff := by
      rw [coeff_C_mul, Polynomial.leadingCoeff,
        naturalLinePoly_natDegree]
      congr 2

/-- A zero top ordinary coefficient converts to a zero top natural
coefficient.  This closes the truncation side condition rather than assuming
it at the sparse routine boundary. -/
theorem convert_top_zero (ordinary : Fin 48 → K)
    (htop : ordinary (47 : Fin 48) = 0) :
    convert ordinary (47 : Fin 48) = 0 := by
  have hequal := congrArg (fun polynomial : K[X] => polynomial.coeff 47)
    (naturalSynthesis_convert ordinary)
  rw [naturalSynthesis_top_coeff, ordinarySynthesis_coeff] at hequal
  have htop' : ordinary ⟨47, by omega⟩ = 0 := by
    rw [show (⟨47, by omega⟩ : Fin 48) = (47 : Fin 48) from Fin.ext rfl]
    exact htop
  simp only [show 47 < 48 by omega, dif_pos, htop'] at hequal
  have hleading : (naturalLinePoly K 47).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (naturalLinePoly_ne_zero (K := K) 47)
  exact (mul_eq_zero.mp hequal).resolve_right hleading

/-- One exact commuting square: sparse natural shift after conversion equals
dense ordinary shift followed by conversion. -/
theorem sparseShift_convert (ordinary : Fin 48 → K)
    (htop : ordinary (47 : Fin 48) = 0) :
    sparseShift (convert ordinary) = convert (ordinaryShift ordinary) := by
  apply naturalSynthesis_injective
  rw [naturalSynthesis_sparseShift _ (convert_top_zero ordinary htop),
    naturalSynthesis_convert, naturalSynthesis_convert,
    ordinarySynthesis_shift ordinary htop]

/-- Ordinary coefficient support is strictly below `bound`. -/
def SupportedBelow (bound : Nat) (coefficients : Fin 48 → K) : Prop :=
  ∀ index : Fin 48, bound ≤ (index : Nat) → coefficients index = 0

omit [NeZero (2 : K)] in
theorem supportedBelow_top_zero {bound : Nat} {coefficients : Fin 48 → K}
    (hsupport : SupportedBelow bound coefficients) (hbound : bound ≤ 47) :
    coefficients (47 : Fin 48) = 0 :=
  hsupport (47 : Fin 48) hbound

omit [NeZero (2 : K)] in
theorem ordinaryShift_supportedBelow {bound : Nat} {coefficients : Fin 48 → K}
    (hsupport : SupportedBelow bound coefficients) :
    SupportedBelow (bound + 1) (ordinaryShift coefficients) := by
  intro index hindex
  rcases Fin.eq_zero_or_eq_succ index with rfl | ⟨previous, rfl⟩
  · simp [ordinaryShift]
  · change coefficients (sourceIndex previous) = 0
    apply hsupport
    change bound + 1 ≤ (previous : Nat) + 1 at hindex
    change bound ≤ (previous : Nat)
    omega

/-- Iteration of the exact sparse routine. -/
def sparseShiftIter : Nat → (Fin 48 → K) → Fin 48 → K
  | 0, coefficients => coefficients
  | steps + 1, coefficients => sparseShift (sparseShiftIter steps coefficients)

/-- Matching iteration in ordinary monomial coordinates. -/
def ordinaryShiftIter : Nat → (Fin 48 → K) → Fin 48 → K
  | 0, coefficients => coefficients
  | steps + 1, coefficients => ordinaryShift (ordinaryShiftIter steps coefficients)

omit [NeZero (2 : K)] in
theorem ordinaryShiftIter_supportedBelow (steps bound : Nat)
    (coefficients : Fin 48 → K)
    (hsupport : SupportedBelow bound coefficients) :
    SupportedBelow (bound + steps) (ordinaryShiftIter steps coefficients) := by
  induction steps with
  | zero => simpa [ordinaryShiftIter] using hsupport
  | succ steps ih =>
      rw [ordinaryShiftIter]
      simpa [Nat.add_assoc] using ordinaryShift_supportedBelow ih

/-- Complete bounded commuting chain.  `bound + steps ≤ 48` proves that every
intermediate source has zero coordinate 47, including the final pre-shift
state; no truncation is implicit. -/
theorem sparseShiftIter_convert (steps bound : Nat)
    (ordinary : Fin 48 → K)
    (hsupport : SupportedBelow bound ordinary)
    (hfit : bound + steps ≤ 48) :
    sparseShiftIter steps (convert ordinary) =
      convert (ordinaryShiftIter steps ordinary) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [sparseShiftIter, ordinaryShiftIter, ih]
      · apply sparseShift_convert
        apply supportedBelow_top_zero
          (ordinaryShiftIter_supportedBelow steps bound ordinary hsupport)
        omega
      · omega

/-- GoodA uses the whole shift chain `0..11` from a degree-at-most-36 kernel,
whose ordinary coefficients are supported below 37. -/
theorem goodA_complete_shift_chain (ordinary : Fin 48 → K)
    (hsupport : SupportedBelow 37 ordinary) (steps : Nat) (hsteps : steps ≤ 11) :
    sparseShiftIter steps (convert ordinary) =
      convert (ordinaryShiftIter steps ordinary) := by
  exact sparseShiftIter_convert steps 37 ordinary hsupport (by omega)

/-- GoodB's shorter `0..3` chain is the corresponding exact specialization. -/
theorem goodB_complete_shift_chain (ordinary : Fin 48 → K)
    (hsupport : SupportedBelow 37 ordinary) (steps : Nat) (hsteps : steps ≤ 3) :
    sparseShiftIter steps (convert ordinary) =
      convert (ordinaryShiftIter steps ordinary) := by
  exact goodA_complete_shift_chain ordinary hsupport steps (by omega)

#print axioms AspisV5GoodGateSparseShift.sparseBasisPolynomial_eq_mul_X
#print axioms AspisV5GoodGateSparseShift.naturalSynthesis_sparseShift
#print axioms AspisV5GoodGateSparseShift.sparseShift_convert
#print axioms AspisV5GoodGateSparseShift.sparseShiftIter_convert
#print axioms AspisV5GoodGateSparseShift.goodA_complete_shift_chain
#print axioms AspisV5GoodGateSparseShift.goodB_complete_shift_chain

end AspisV5GoodGateSparseShift
