import Mathlib

/-!
# Algebraic equivalences for the retained low-bloat CU rewrites

This leaf module records the ring identities behind five arithmetic rewrites in
the current Rust verifier tree:

* `circle_fri::double_point` uses complex squaring instead of generic point
  addition with equal operands;
* `circle_fri::evaluate_final_line_tensor` evaluates the nonconstant three
  terms as one lazy limb dot and adds the constant coefficient afterwards;
* `atomic_state_only_terminal::routing_linear_form` routes coefficients `1`
  and `P - 1` through addition and subtraction instead of generic scalar
  multiplication;
* `LegacyAtomicSelectors::copy_active` evaluates a dense selector mask by
  subtracting its smaller complement from the total equality-basis sum `1`;
* the atomic copy-power table reuses a prepared multiplier for `lambda` while
  retaining the ordinary repeated-multiplication recurrence;
* the Poseidon residual linear combination is factored by selector class; and
* the one- and two-step FRI parent-doubling branches specialize a single
  abstract iteration recurrence.

The final section also mirrors the exponent schedule in `M31::inv`.  These are
pure algebraic statements.  Identifying Rust `M31`/`QM31`, prepared Karatsuba
channels, canonical reduction, selector tables, and loops with this model is a
separate executable-correspondence obligation.
-/

open scoped BigOperators

namespace AspisV5CuArithmeticEquivalences

/-! ## Specialized complex squaring -/

/-- The real coordinate of `(x + yi)^2` computed by the deployed two-product
complex-square kernel. -/
theorem complex_square_real_coordinate {R : Type*} [CommRing R] (x y : R) :
    (x + y) * (x - y) = x * x - y * y := by
  ring

/-- The imaginary coordinate of `(x + yi)^2`: adding the two equal cross
products is multiplication by two. -/
theorem complex_square_imaginary_coordinate {R : Type*} [CommRing R] (x y : R) :
    x * y + y * x = (2 : R) * x * y := by
  ring

/-! ## Final tensor: four terms as a constant plus a lazy three-term dot -/

/-- Regroup the natural final line-tensor evaluation
`c0*1 + c1*x + c2*pi(x) + c3*x*pi(x)` into the exact deployed spelling:
the constant coefficient plus one lazy three-term limb dot.  `piX` and `xPiX`
are kept explicit because their optimized M31 construction is independent of
this additive regrouping. -/
theorem final_tensor_four_term_eq_constant_add_lazy_dot3
    {R : Type*} [CommRing R]
    (c0 c1 c2 c3 x piX xPiX : R) :
    c0 * 1 + c1 * x + c2 * piX + c3 * xPiX =
      c0 + (c1 * x + c2 * piX + c3 * xPiX) := by
  ring

/-! ## Exact `+1` and `-1` routing branches -/

/-- The coefficient-`1` routing branch is generic scalar multiplication by
one. -/
theorem routing_plus_one_branch_eq_generic_smul
    {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M] (value : M) :
    (1 : S) • value = value := by
  simp

/-- The M31 coefficient `P - 1` denotes `-1`; the subtraction routing branch
is therefore generic scalar multiplication by minus one. -/
theorem routing_minus_one_branch_eq_generic_smul
    {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M] (value : M) :
    (-1 : S) • value = -value := by
  simp

/-- The canonical M31 integer used by the Rust `P - 1` branch is literally
minus one in the deployed field. -/
theorem m31_p_minus_one_eq_neg_one :
    ((2147483646 : ℕ) : ZMod 2147483647) = -1 := by
  rw [show 2147483646 = 2147483647 - 1 by norm_num]
  rw [Nat.cast_sub (by norm_num : 1 ≤ 2147483647)]
  rw [ZMod.natCast_self]
  simp

/-- Three maximal canonical M31 products fit in one `u64`, justifying the
single-reduction boundary of the retained lazy three-term limb dot. -/
theorem m31_lazy_dot3_fits_u64 :
    3 * (2147483647 - 1) ^ 2 < 2 ^ 64 := by
  norm_num

/-! ## Dense selector masks through their complements -/

/-- If a complete equality basis sums to one, the sum selected by a dense mask
is one minus the sum on the mask's complement.  This is the algebraic identity
used by the 64-entry high-selector optimization. -/
theorem selected_sum_eq_one_sub_complement_sum
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (values : ι → R) (selected : Finset ι)
    (hTotal : ∑ index, values index = 1) :
    (∑ index ∈ selected, values index) =
      1 - ∑ index ∈ selectedᶜ, values index := by
  rw [eq_sub_iff_add_eq, ← hTotal]
  exact Finset.sum_add_sum_compl selected values

/-- The named total-sum hypothesis above is non-vacuous on every explicitly
pointed finite index type (in particular `Fin 64`): put all mass at `pivot`. -/
theorem total_sum_one_hypothesis_nonvacuous
    {ι R : Type*} [Fintype ι] [CommRing R] (pivot : ι) :
    ∃ values : ι → R, ∑ index, values index = 1 := by
  classical
  refine ⟨fun index ↦ if index = pivot then 1 else 0, ?_⟩
  simp

/-! ## Prepared repeated multiplication -/

/-- The pre-optimization copy-power recurrence.  Entry zero is `lambda`, and
every later entry multiplies the previous entry by `lambda` on the right. -/
def ordinaryMulRecurrence {R : Type*} [Mul R] (lambda : R) : ℕ → R
  | 0 => lambda
  | n + 1 => ordinaryMulRecurrence lambda n * lambda

/-- The retained recurrence, parameterized by the action of the cached
`PreparedQm31Multiplier(lambda)`. -/
def preparedMulRecurrence {R : Type*} (lambda : R) (preparedMul : R → R) : ℕ → R
  | 0 => lambda
  | n + 1 => preparedMul (preparedMulRecurrence lambda preparedMul n)

/-- If the prepared multiplier implements left multiplication by `lambda`, its
entire repeated-multiplication table is pointwise identical to the ordinary
right-multiplication recurrence.  Commutativity is exactly what aligns the two
operand orders used by the Rust spellings. -/
theorem prepared_repeated_mul_recurrence_eq_ordinary
    {R : Type*} [CommMonoid R] (lambda : R) (preparedMul : R → R)
    (hPrepared : ∀ value, preparedMul value = lambda * value) :
    ∀ n, preparedMulRecurrence lambda preparedMul n = ordinaryMulRecurrence lambda n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [preparedMulRecurrence, ordinaryMulRecurrence, hPrepared, ih, mul_comm]

/-- The prepared-multiplier correctness premise is itself satisfiable: the
ordinary left-multiplication function is a witness. -/
theorem prepared_mul_correctness_hypothesis_nonvacuous
    {R : Type*} [Mul R] (lambda : R) :
    ∃ preparedMul : R → R, ∀ value, preparedMul value = lambda * value := by
  exact ⟨fun value ↦ lambda * value, fun _ ↦ rfl⟩

/-! ## Poseidon residual factorization -/

/-- Factor the residual linear combination by selector class.  The sole
hypothesis records the exact partition of the active selector into leading,
full-round, and internal-round selectors; no approximation or field-specific
identity is involved. -/
theorem poseidon_residual_factorization
    {R : Type*} [CommRing R]
    (active leading full internal target leadingValue fullValue internalValue : R)
    (hActive : active = leading + full + internal) :
    active * target - leading * leadingValue - full * fullValue - internal * internalValue =
      leading * (target - leadingValue) +
        full * (target - fullValue) +
          internal * (target - internalValue) := by
  rw [hActive]
  ring

/-- The selector-partition premise of `poseidon_residual_factorization` is
satisfiable for arbitrary selector-class values. -/
theorem poseidon_active_partition_hypothesis_nonvacuous
    {R : Type*} [CommRing R] (leading full internal : R) :
    ∃ active, active = leading + full + internal := by
  exact ⟨leading + full + internal, rfl⟩

/-! ## FRI parent-doubling control flow -/

/-- Apply an abstract parent-doubling operation exactly `count` times.  This
models only the control-flow recurrence, not the deployed Rust point type or
its doubling implementation. -/
def iterateParentDouble {Point : Type*} (double : Point → Point) :
    ℕ → Point → Point
  | 0, point => point
  | count + 1, point => iterateParentDouble double count (double point)

/-- The direct control-flow spelling: always compute the first parent and
compute the second parent exactly when the Boolean branch requests it. -/
def firstThenConditionalSecondParent {Point : Type*}
    (double : Point → Point) (needsSecond : Bool) (point : Point) : Point :=
  let firstParent := double point
  if needsSecond then double firstParent else firstParent

/-- A one-parent iteration is exactly the direct spelling with the second
doubling branch disabled. -/
theorem iterate_parent_double_one_eq_direct
    {Point : Type*} (double : Point → Point) (point : Point) :
    iterateParentDouble double 1 point =
      firstThenConditionalSecondParent double false point := by
  rfl

/-- A two-parent iteration is exactly the direct spelling with the second
doubling branch enabled. -/
theorem iterate_parent_double_two_eq_direct
    {Point : Type*} (double : Point → Point) (point : Point) :
    iterateParentDouble double 2 point =
      firstThenConditionalSecondParent double true point := by
  rfl

/-! ## M31 inverse addition-chain exponent -/

/-- Squaring a value `count` times multiplies its represented exponent by
`2^count`. -/
def squareNExponent (exponent count : ℕ) : ℕ := exponent * 2 ^ count

/-- Exponents of all temporaries in the retained `M31::inv` schedule.  Product
is exponent addition and each call to `square_n` is represented by
`squareNExponent`. -/
structure M31InverseAdditionChain where
  t2 : ℕ
  t4 : ℕ
  t8 : ℕ
  t16 : ℕ
  t24 : ℕ
  t28 : ℕ
  t29 : ℕ
  t30 : ℕ
  result : ℕ
  deriving DecidableEq, Repr

/-- Exact transcription of the Rust `t2` through final-result exponent
schedule, beginning with input exponent one. -/
def m31InverseAdditionChain : M31InverseAdditionChain :=
  let t2 := 1 + 1 + 1
  let t4 := squareNExponent t2 2 + t2
  let t8 := squareNExponent t4 4 + t4
  let t16 := squareNExponent t8 8 + t8
  let t24 := squareNExponent t16 8 + t8
  let t28 := squareNExponent t24 4 + t4
  let t29 := t28 + t28 + 1
  let t30 := t29 + t29
  let result := t30 + t30 + 1
  { t2, t4, t8, t16, t24, t28, t29, t30, result }

/-- The M31 modulus `P = 2^31 - 1`, at the exponent level. -/
def m31Prime : ℕ := 2 ^ 31 - 1

/-- Every named schedule point has the intended exponent, and the final one is
`2^31 - 3 = P - 2`. -/
theorem m31_inverse_addition_chain_schedule_eq :
    m31InverseAdditionChain =
      { t2 := 2 ^ 2 - 1
        t4 := 2 ^ 4 - 1
        t8 := 2 ^ 8 - 1
        t16 := 2 ^ 16 - 1
        t24 := 2 ^ 24 - 1
        t28 := 2 ^ 28 - 1
        t29 := 2 ^ 29 - 1
        t30 := 2 ^ 30 - 2
        result := m31Prime - 2 } := by
  norm_num [m31InverseAdditionChain, squareNExponent, m31Prime]

/-- In particular, the exponent returned by the retained addition chain is
Fermat's inverse exponent `P - 2`. -/
theorem m31_inverse_addition_chain_exponent_eq :
    m31InverseAdditionChain.result = m31Prime - 2 := by
  rw [m31_inverse_addition_chain_schedule_eq]

#print axioms complex_square_real_coordinate
#print axioms complex_square_imaginary_coordinate
#print axioms final_tensor_four_term_eq_constant_add_lazy_dot3
#print axioms routing_plus_one_branch_eq_generic_smul
#print axioms routing_minus_one_branch_eq_generic_smul
#print axioms m31_p_minus_one_eq_neg_one
#print axioms m31_lazy_dot3_fits_u64
#print axioms selected_sum_eq_one_sub_complement_sum
#print axioms total_sum_one_hypothesis_nonvacuous
#print axioms prepared_repeated_mul_recurrence_eq_ordinary
#print axioms prepared_mul_correctness_hypothesis_nonvacuous
#print axioms poseidon_residual_factorization
#print axioms poseidon_active_partition_hypothesis_nonvacuous
#print axioms iterate_parent_double_one_eq_direct
#print axioms iterate_parent_double_two_eq_direct
#print axioms m31_inverse_addition_chain_schedule_eq
#print axioms m31_inverse_addition_chain_exponent_eq

end AspisV5CuArithmeticEquivalences
