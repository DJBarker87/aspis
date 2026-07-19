import Mathlib

/-!
# Algebraic equivalences for the retained low-bloat CU rewrites

This leaf module records the ring identities behind the arithmetic rewrites in
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
* the atomic semantic terminal uses specialized square residuals, reverse
  radix-two Horner reconstruction, frozen selector complements, and common
  selector factors without changing the represented polynomial;
* the atomic copy-power table reuses a prepared multiplier for `lambda` while
  retaining the ordinary repeated-multiplication recurrence;
* the Poseidon residual linear combination is factored by selector class; and
* the one- and two-step FRI parent-doubling branches specialize a single
  abstract iteration recurrence;
* the fixed four-lane Poseidon matrix is consumed through the adjoint of the
  four tower-packing functionals; and
* a pre-grouped public lookup is substituted for its original table only
  under an explicit pointwise table-equality premise.

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

/-! ## Exact atomic semantic-terminal rewrites -/

/-- The specialized square-and-subtract spelling of a Boolean residual is
exactly the original `x * (x - 1)` polynomial. -/
theorem boolean_square_residual_eq_mul_sub_one
    {R : Type*} [CommRing R] (x : R) :
    x * x - x = x * (x - 1) := by
  ring

/-- The exact ten-limb reverse Horner loop used by
`atomic_state_only_terminal::atomic_reconstruct_10`.  The input function is in
little-endian order; the loop starts at limb nine and consumes limbs eight
through zero. -/
def reverseRadix2Horner10 {R : Type*} [Add R] (bit : Fin 10 → R) : R :=
  [bit 8, bit 7, bit 6, bit 5, bit 4, bit 3, bit 2, bit 1, bit 0].foldl
    (fun accumulator next ↦ accumulator + accumulator + next) (bit 9)

/-- Reverse radix-two Horner evaluation is the exact little-endian weighted
sum used by the arithmetization, for arbitrary (including non-Boolean) field
values. -/
theorem reverse_radix2_horner10_eq_little_endian
    {R : Type*} [CommSemiring R] (bit : Fin 10 → R) :
    reverseRadix2Horner10 bit =
      ∑ index : Fin 10, bit index * (2 : R) ^ (index : ℕ) := by
  simp [reverseRadix2Horner10, Fin.sum_univ_succ]
  ring

/-- Split a complete equality-basis mass into the four consecutive blocks
`[0,4)`, `[4,44)`, `[44,49)`, and `[49,64)`.  Subtracting the tail to obtain
the Poseidon prefix, then subtracting its two side blocks, returns exactly the
middle path-block mass. -/
theorem middle_block_eq_one_sub_tail_sub_sides
    {R : Type*} [CommRing R] (left middle right tail : R)
    (hTotal : left + middle + right + tail = 1) :
    1 - tail - left - right = middle := by
  rw [← hTotal]
  ring

/-- Two contributions sharing both an outer selector and a packed residual
may be evaluated with one multiplication by the sum of their inner selectors.
This is the exact factorization used by the initial and absorption blocks. -/
theorem common_selector_factorization
    {R : Type*} [CommRing R] (selector left right packed : R) :
    (selector * left) * packed + (selector * right) * packed =
      (selector * (left + right)) * packed := by
  ring

/-- Fuse two adjacent packed range lanes before applying their common
selector.  `basis` is the second lane's fixed tower-packing weight; keeping it
abstract makes clear that this is distributivity, not a property special to a
chosen field representation. -/
theorem range_pack_two_lane_fusion
    {R : Type*} [CommRing R] (selector basis first second : R) :
    selector * first + basis * (selector * second) =
      selector * (first + basis * second) := by
  ring

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

/-! ## Fixed external matrix followed by tower packing -/

/-- The deployed four-lane local external matrix. -/
def externalLocalMatrix (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![2, 3, 1, 1;
     1, 2, 3, 1;
     1, 1, 2, 3;
     3, 1, 1, 2]

/-- The four fixed coefficient matrices describing the output limbs of the
tower pack `(1, i, u, i*u)`.  Rows select a local-matrix output lane and
columns select one of that lane's four base-field limbs.  For example, row
zero is the `t[0,*]` contribution and the first matrix encodes
`t[0,a] - t[1,b] + 2*t[2,c] - t[2,d] - t[3,c] - 2*t[3,d]`. -/
def towerPackWeight (R : Type*) [CommRing R] :
    Fin 4 → Matrix (Fin 4) (Fin 4) R :=
  ![
    !![1, 0, 0, 0;
       0, -1, 0, 0;
       0, 0, 2, -1;
       0, 0, -1, -2],
    !![0, 1, 0, 0;
       1, 0, 0, 0;
       0, 0, 1, 2;
       0, 0, 2, -1],
    !![0, 0, 1, 0;
       0, 0, 0, -1;
       1, 0, 0, 0;
       0, -1, 0, 0],
    !![0, 0, 0, 1;
       0, 0, 1, 0;
       0, 1, 0, 0;
       1, 0, 0, 0]
  ]

/-- Frobenius pairing of a coefficient matrix with a four-by-four limb
matrix. -/
def matrixFunctional {R : Type*} [CommRing R]
    (weight value : Matrix (Fin 4) (Fin 4) R) : R :=
  ∑ row, ∑ limb, weight row limb * value row limb

/-- Applying the local matrix and then any one of the four tower-pack
functionals is exactly applying the transposed local matrix to that functional
first.  This is the fixed direct packed-adjoint identity; the proof expands
all four cases and normalizes the resulting nontrivial ring expressions. -/
theorem external_local_then_tower_pack_eq_adjoint
    {R : Type*} [CommRing R]
    (input : Matrix (Fin 4) (Fin 4) R) (packedLimb : Fin 4) :
    matrixFunctional (towerPackWeight R packedLimb)
        (externalLocalMatrix R * input) =
      matrixFunctional
        ((externalLocalMatrix R).transpose * towerPackWeight R packedLimb)
        input := by
  fin_cases packedLimb <;>
    simp [matrixFunctional, towerPackWeight, externalLocalMatrix,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

/-- The coarser raw packed-output bound used by the executable implementation
fits in an unsigned 64-bit accumulator. -/
theorem external_local_packed_56p_fits_u64 :
    56 * 2147483647 < 2 ^ 64 := by
  norm_num

/-- Before adding zero-modulus offsets, a local-matrix output limb is at most
the row coefficient sum `7` times the largest canonical M31 representative.
This sharper source bound is strictly below the implementation's `7P`
modulus bound. -/
theorem external_local_canonical_source_bound :
    7 * (2147483647 - 1) < 7 * 2147483647 := by
  norm_num

/-- Even eight copies of the sharper canonical local-limb maximum fit in a
`u64`; the executable path uses the slightly looser but simpler `56P` bound
above. -/
theorem external_local_sharp_eightfold_fits_u64 :
    8 * (7 * (2147483647 - 1)) < 2 ^ 64 := by
  norm_num

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

/-! ## Exact pre-grouped public lookups -/

/-- Look up a row through a precomputed group assignment and group table. -/
def preGroupedLookup {Row Group Value : Type*}
    (rowGroup : Row → Group) (groupTable : Group → Value) (row : Row) : Value :=
  groupTable (rowGroup row)

/-- A pre-grouped lookup is pointwise identical to the original lookup when
the supplied public group table is explicitly certified to reproduce every
original row.  No deployed row-group constants are asserted here. -/
theorem pre_grouped_lookup_eq_original
    {Row Group Value : Type*}
    (original : Row → Value) (rowGroup : Row → Group)
    (groupTable : Group → Value)
    (hTable : ∀ row, groupTable (rowGroup row) = original row) :
    ∀ row, preGroupedLookup rowGroup groupTable row = original row := by
  intro row
  exact hTable row

/-- Consequently, replacing the original lookup inside any finite weighted
linear relation preserves that relation exactly.  This captures the accepted
pre-grouping optimization while leaving the frozen Rust table equality as an
explicit executable-correspondence obligation. -/
theorem pre_grouped_linear_lookup_eq_original
    {Row Group R : Type*} [Fintype Row] [CommRing R]
    (original : Row → R) (rowGroup : Row → Group)
    (groupTable : Group → R) (weight : Row → R)
    (hTable : ∀ row, groupTable (rowGroup row) = original row) :
    (∑ row, weight row * preGroupedLookup rowGroup groupTable row) =
      ∑ row, weight row * original row := by
  apply Finset.sum_congr rfl
  intro row _
  rw [pre_grouped_lookup_eq_original original rowGroup groupTable hTable row]

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

/-! ## Fixed 7-coefficient Horner zero-seed elimination -/

/-- The pre-optimization fixed-width Horner fold with a redundant zero seed:
`((((((0*x + c6)*x + c5)*x + c4)*x + c3)*x + c2)*x + c1)*x + c0`.  The leading
`0 * x + c6` step is the one the retained verifier eliminates. -/
def horner7ZeroSeed {R : Type*} [CommSemiring R] (x : R) (c : Fin 7 → R) : R :=
  ((((((0 * x + c 6) * x + c 5) * x + c 4) * x + c 3) * x + c 2) * x + c 1) * x + c 0

/-- The retained fold: seed directly at the leading coefficient `c6` and consume
only `c5 … c0`, saving one multiply-add per evaluation. -/
def horner7Optimized {R : Type*} [CommSemiring R] (x : R) (c : Fin 7 → R) : R :=
  (((((c 6 * x + c 5) * x + c 4) * x + c 3) * x + c 2) * x + c 1) * x + c 0

/-- Zero-seed elimination is exact: the two fixed-width folds agree for every
`CommSemiring R`, every point `x : R`, and every coefficient vector
`c : Fin 7 → R`. -/
theorem horner7_zero_seed_eq_optimized {R : Type*} [CommSemiring R]
    (x : R) (c : Fin 7 → R) :
    horner7ZeroSeed x c = horner7Optimized x c := by
  simp only [horner7ZeroSeed, horner7Optimized, zero_mul, zero_add]

/-- The common value of both folds is the represented degree-six polynomial
`∑ i : Fin 7, c i * x ^ i`. -/
theorem horner7_eq_poly {R : Type*} [CommSemiring R]
    (x : R) (c : Fin 7 → R) :
    horner7Optimized x c = ∑ i : Fin 7, c i * x ^ (i : ℕ) := by
  simp [horner7Optimized, Fin.sum_univ_seven]
  ring

/-! ## Degree-27 boundary limb accumulation -/

/-- With `P = 2147483647` and 28 canonical natural limbs (`a i < P`), the boundary
accumulator `2·a₀ + (a₁ + … + a₂₇)` stays strictly below `2^36`, so the deployed
`u64` boundary-limb accumulator never overflows.  Stated for arbitrary canonical
limbs, not only constants. -/
theorem cu_boundary_accumulator_bound (a : Fin 28 → ℕ)
    (ha : ∀ i, a i < 2147483647) :
    2 * a 0 + ∑ i : Fin 27, a i.succ < 2 ^ 36 := by
  have hsum : ∑ i : Fin 27, a i.succ ≤ 27 * (2147483647 - 1) := by
    calc ∑ i : Fin 27, a i.succ
        ≤ ∑ _i : Fin 27, (2147483647 - 1) :=
          Finset.sum_le_sum (fun i _ => by have := ha i.succ; omega)
      _ = 27 * (2147483647 - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h0 := ha 0
  rw [show (2 : ℕ) ^ 36 = 68719476736 from by norm_num]
  omega

/-- The same natural accumulator reduces, in `ZMod P`, to exactly
`p(0) + p(1) = a₀ + ∑ᵢ aᵢ` — the degree-27 boundary functional the sumcheck
endpoint compares.  The two naturals are literally equal
(`2·a₀ + ∑_{i≥1} aᵢ = a₀ + ∑ᵢ aᵢ`), so the residue is exact. -/
theorem cu_boundary_accumulator_cast (a : Fin 28 → ℕ) :
    ((2 * a 0 + ∑ i : Fin 27, a i.succ : ℕ) : ZMod 2147483647) =
      (a 0 : ZMod 2147483647) + ∑ i : Fin 28, ((a i : ℕ) : ZMod 2147483647) := by
  have hnat : 2 * a 0 + ∑ i : Fin 27, a i.succ = a 0 + ∑ i : Fin 28, a i := by
    have he : ∑ i : Fin 28, a i = a 0 + ∑ i : Fin 27, a i.succ := by
      rw [Fin.sum_univ_succ]
    rw [he]
    ring
  rw [hnat]
  push_cast
  ring

/-- Sharp tooth: even the worst case (every limb equal to the maximal canonical
representative `P - 1`) satisfies the accumulator bound, obtained by applying the
general theorem. -/
theorem cu_boundary_accumulator_bound_all_max :
    2 * (2147483647 - 1) + ∑ _i : Fin 27, (2147483647 - 1) < 2 ^ 36 := by
  exact cu_boundary_accumulator_bound (fun _ : Fin 28 => 2147483647 - 1)
    (fun _ => by omega)

#print axioms horner7_zero_seed_eq_optimized
#print axioms horner7_eq_poly
#print axioms cu_boundary_accumulator_bound
#print axioms cu_boundary_accumulator_cast
#print axioms cu_boundary_accumulator_bound_all_max

#print axioms complex_square_real_coordinate
#print axioms complex_square_imaginary_coordinate
#print axioms final_tensor_four_term_eq_constant_add_lazy_dot3
#print axioms routing_plus_one_branch_eq_generic_smul
#print axioms routing_minus_one_branch_eq_generic_smul
#print axioms m31_p_minus_one_eq_neg_one
#print axioms m31_lazy_dot3_fits_u64
#print axioms selected_sum_eq_one_sub_complement_sum
#print axioms total_sum_one_hypothesis_nonvacuous
#print axioms boolean_square_residual_eq_mul_sub_one
#print axioms reverse_radix2_horner10_eq_little_endian
#print axioms middle_block_eq_one_sub_tail_sub_sides
#print axioms common_selector_factorization
#print axioms range_pack_two_lane_fusion
#print axioms prepared_repeated_mul_recurrence_eq_ordinary
#print axioms prepared_mul_correctness_hypothesis_nonvacuous
#print axioms poseidon_residual_factorization
#print axioms poseidon_active_partition_hypothesis_nonvacuous
#print axioms external_local_then_tower_pack_eq_adjoint
#print axioms external_local_packed_56p_fits_u64
#print axioms external_local_canonical_source_bound
#print axioms external_local_sharp_eightfold_fits_u64
#print axioms iterate_parent_double_one_eq_direct
#print axioms iterate_parent_double_two_eq_direct
#print axioms pre_grouped_lookup_eq_original
#print axioms pre_grouped_linear_lookup_eq_original
#print axioms m31_inverse_addition_chain_schedule_eq
#print axioms m31_inverse_addition_chain_exponent_eq

end AspisV5CuArithmeticEquivalences
