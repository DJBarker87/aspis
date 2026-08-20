import V5FriPreparedSumSemantics

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

/-!
# Exact semantics of the production V5 FRI folds

This file follows the successful path through the extracted Rust arithmetic
helpers.  It proves the value returned by the optimized arity-four fold from
the primitive field-operation theorems and the exact prepared-dot-product
theorem.  No fold result is supplied as a premise.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriFoldSemantics

open AspisV5FriArithmeticSemantics
open AspisV5FriPreparedSumSemantics

namespace Fresh
open V5FriArithmeticExact

abbrev M31 := field.M31
abbrev QM31 := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier

end Fresh

def CanonicalQM31Array4 (values : Array Fresh.QM31 4#usize) : Prop :=
  ∀ index, index < 4 → canonicalQM31 values.val[index]!

def CanonicalM31Array3 (values : Array Fresh.M31 3#usize) : Prop :=
  ∀ index, index < 3 → canonicalM31 values.val[index]!

private theorem m31View_eq_algebraMap (x : Fresh.M31) :
    m31View x =
      algebraMap ExactM31 ExactQM31 ((x.val : Nat) : ExactM31) := by
  rfl

private theorem prepared_dot_three
    (alpha linear quadratic cubic : ExactQM31)
    (linearRaw quadraticRaw cubicRaw : Fresh.QM31)
    (hLinear : qm31View linearRaw = linear)
    (hQuadratic : qm31View quadraticRaw = quadratic)
    (hCubic : qm31View cubicRaw = cubic) :
    exactPreparedProductDot (fun i => alpha ^ (i + 1))
        (Array.make 3#usize [linearRaw, quadraticRaw, cubicRaw]) =
      alpha * linear + alpha ^ 2 * quadratic + alpha ^ 3 * cubic := by
  have h0 :
      (Array.make 3#usize [linearRaw, quadraticRaw, cubicRaw]).val[0]! =
        linearRaw := by rfl
  have h1 :
      (Array.make 3#usize [linearRaw, quadraticRaw, cubicRaw]).val[1]! =
        quadraticRaw := by rfl
  have h2 :
      (Array.make 3#usize [linearRaw, quadraticRaw, cubicRaw]).val[2]! =
        cubicRaw := by rfl
  simp only [exactPreparedProductDot, Finset.sum_range_succ]
  rw [h0, h1, h2, hLinear, hQuadratic, hCubic]
  ring

/-- Successful execution of the extracted optimized arity-four polynomial
helper returns exactly the nested normalized line fold. -/
theorem normalized_candidate_corresponds
    (values : Array Fresh.QM31 4#usize)
    (alphaPowers : Array Fresh.Prepared 3#usize)
    (inverses : Array Fresh.M31 3#usize)
    (alpha : ExactQM31)
    (hValues : CanonicalQM31Array4 values)
    (hInverses : CanonicalM31Array3 inverses)
    (hAlphaPowers : PreparedArrayRepresents alphaPowers
      (fun i => alpha ^ (i + 1))) :
    ∃ out : Fresh.QM31,
      V5FriArithmeticExact.circle_fri.normalized_arity4_prepared_polynomial_candidate
          values alphaPowers inverses = ok out ∧
      canonicalQM31 out ∧
      qm31View out =
        AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
          (m31View inverses.val[0]!) (m31View inverses.val[1]!)
          (m31View inverses.val[2]!)
          (fun i => qm31View values.val[i.val]!) := by
  have hv0 := hValues 0 (by norm_num)
  have hv1 := hValues 1 (by norm_num)
  have hv2 := hValues 2 (by norm_num)
  have hv3 := hValues 3 (by norm_num)
  have hi0 := hInverses 0 (by norm_num)
  have hi1 := hInverses 1 (by norm_num)
  have hi2 := hInverses 2 (by norm_num)
  have hq0 := generated_array_index_run values 0#usize (by norm_num)
  have hq1 := generated_array_index_run values 1#usize (by norm_num)
  have hq2 := generated_array_index_run values 2#usize (by norm_num)
  have hq3 := generated_array_index_run values 3#usize (by norm_num)
  have hinv0 := generated_array_index_run inverses 0#usize (by norm_num)
  have hinv1 := generated_array_index_run inverses 1#usize (by norm_num)
  have hinv2 := generated_array_index_run inverses 2#usize (by norm_num)
  rcases qm31_add_corresponds values.val[0]! values.val[1]! hv0 hv1 with
    ⟨leftSum, hLeftSum, hLeftSumCanonical, hLeftSumExact⟩
  rcases qm31_add_corresponds values.val[2]! values.val[3]! hv2 hv3 with
    ⟨rightSum, hRightSum, hRightSumCanonical, hRightSumExact⟩
  rcases qm31_sub_corresponds values.val[0]! values.val[1]! hv0 hv1 with
    ⟨leftDifference, hLeftDifference, hLeftDifferenceCanonical,
      hLeftDifferenceExact⟩
  rcases qm31_mul_m31_corresponds leftDifference inverses.val[0]!
      hLeftDifferenceCanonical hi0 with
    ⟨leftScaled, hLeftScaled, hLeftScaledCanonical, hLeftScaledExact⟩
  rcases qm31_sub_corresponds values.val[2]! values.val[3]! hv2 hv3 with
    ⟨rightDifference, hRightDifference, hRightDifferenceCanonical,
      hRightDifferenceExact⟩
  rcases qm31_mul_m31_corresponds rightDifference inverses.val[1]!
      hRightDifferenceCanonical hi1 with
    ⟨rightScaled, hRightScaled, hRightScaledCanonical, hRightScaledExact⟩
  rcases qm31_add_corresponds leftSum rightSum hLeftSumCanonical
      hRightSumCanonical with
    ⟨totalSum, hTotalSum, hTotalSumCanonical, hTotalSumExact⟩
  rcases qm31_half_corresponds totalSum hTotalSumCanonical with
    ⟨halfTotal, hHalfTotal, hHalfTotalCanonical, hHalfTotalExact⟩
  rcases qm31_half_corresponds halfTotal hHalfTotalCanonical with
    ⟨constant, hConstant, hConstantCanonical, hConstantExact⟩
  rcases qm31_add_corresponds leftScaled rightScaled hLeftScaledCanonical
      hRightScaledCanonical with
    ⟨scaledSum, hScaledSum, hScaledSumCanonical, hScaledSumExact⟩
  rcases qm31_half_corresponds scaledSum hScaledSumCanonical with
    ⟨linear, hLinear, hLinearCanonical, hLinearExact⟩
  rcases qm31_sub_corresponds leftSum rightSum hLeftSumCanonical
      hRightSumCanonical with
    ⟨sumDifference, hSumDifference, hSumDifferenceCanonical,
      hSumDifferenceExact⟩
  rcases qm31_half_corresponds sumDifference hSumDifferenceCanonical with
    ⟨halfSumDifference, hHalfSumDifference, hHalfSumDifferenceCanonical,
      hHalfSumDifferenceExact⟩
  rcases qm31_mul_m31_corresponds halfSumDifference inverses.val[2]!
      hHalfSumDifferenceCanonical hi2 with
    ⟨quadratic, hQuadratic, hQuadraticCanonical, hQuadraticExact⟩
  rcases qm31_sub_corresponds leftScaled rightScaled hLeftScaledCanonical
      hRightScaledCanonical with
    ⟨scaledDifference, hScaledDifference, hScaledDifferenceCanonical,
      hScaledDifferenceExact⟩
  rcases qm31_mul_m31_corresponds scaledDifference inverses.val[2]!
      hScaledDifferenceCanonical hi2 with
    ⟨cubic, hCubic, hCubicCanonical, hCubicExact⟩
  let terms : Array Fresh.QM31 3#usize :=
    Array.make 3#usize [linear, quadratic, cubic]
  have hTermsCanonical : CanonicalQM31Array3 terms := by
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases hCases with rfl | rfl | rfl
    all_goals
      simp only [terms, Aeneas.Std.Array.make]
    all_goals assumption
  rcases qm31_sum_products3_prepared_corresponds alphaPowers terms
      (fun i => alpha ^ (i + 1)) hAlphaPowers hTermsCanonical with
    ⟨dot, hDot, hDotCanonical, hDotExact⟩
  rcases qm31_add_corresponds constant dot hConstantCanonical hDotCanonical with
    ⟨out, hOut, hOutCanonical, hOutExact⟩
  refine ⟨out, ?_, hOutCanonical, ?_⟩
  · unfold
      V5FriArithmeticExact.circle_fri.normalized_arity4_prepared_polynomial_candidate
    rw [hq0]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hq1]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hLeftSum]
    simp only [bind_tc_ok]
    rw [hq2]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hq3]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hRightSum]
    simp only [bind_tc_ok]
    rw [hLeftDifference]
    simp only [bind_tc_ok]
    rw [hinv0]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hLeftScaled]
    simp only [bind_tc_ok]
    rw [hRightDifference]
    simp only [bind_tc_ok]
    rw [hinv1]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hRightScaled]
    simp only [bind_tc_ok]
    rw [hTotalSum]
    simp only [bind_tc_ok]
    rw [hHalfTotal]
    simp only [bind_tc_ok]
    rw [hConstant]
    simp only [bind_tc_ok]
    rw [hScaledSum]
    simp only [bind_tc_ok]
    rw [hLinear]
    simp only [bind_tc_ok]
    rw [hSumDifference]
    simp only [bind_tc_ok]
    rw [hHalfSumDifference]
    simp only [bind_tc_ok]
    rw [hinv2]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hQuadratic]
    simp only [bind_tc_ok]
    rw [hScaledDifference]
    simp only [bind_tc_ok]
    rw [hCubic]
    simp only [bind_tc_ok]
    change
      (do
        let q ← V5FriArithmeticExact.field.qm31_sum_products3_prepared
          alphaPowers terms
        V5FriArithmeticExact.field.QM31.add constant q) = ok out
    rw [hDot]
    simp only [bind_tc_ok]
    rw [hOut]
  · rw [hOutExact]
    rw [AspisV5ComponentCConcreteFoldLinearity.lineFoldValue_eq_polynomial]
    unfold AspisV5ComponentCConcreteFoldLinearity.lineFoldPolynomialValue
    rw [hConstantExact, hHalfTotalExact, hTotalSumExact,
      hLeftSumExact, hRightSumExact, hDotExact]
    have hPreparedDot := prepared_dot_three alpha
      (qm31View linear) (qm31View quadratic) (qm31View cubic)
      linear quadratic cubic rfl rfl rfl
    change exactPreparedProductDot (fun i => alpha ^ (i + 1)) terms = _ at hPreparedDot
    rw [hPreparedDot, hLinearExact, hScaledSumExact, hLeftScaledExact,
      hRightScaledExact, hQuadraticExact, hHalfSumDifferenceExact,
      hSumDifferenceExact, hCubicExact, hScaledDifferenceExact,
      hLeftDifferenceExact, hRightDifferenceExact]
    simp only [hLeftSumExact, hRightSumExact, hLeftScaledExact,
      hRightScaledExact, hLeftDifferenceExact, hRightDifferenceExact]
    norm_num
    ring

/-- The source wrapper for a line fold has no additional arithmetic: it
passes the three twiddles to the proved polynomial helper unchanged. -/
theorem normalized_line_corresponds
    (values : Array Fresh.QM31 4#usize)
    (alphaPowers : Array Fresh.Prepared 3#usize)
    (inverses : Array Fresh.M31 3#usize)
    (alpha : ExactQM31)
    (hValues : CanonicalQM31Array4 values)
    (hInverses : CanonicalM31Array3 inverses)
    (hAlphaPowers : PreparedArrayRepresents alphaPowers
      (fun i => alpha ^ (i + 1))) :
    ∃ out : Fresh.QM31,
      V5FriArithmeticExact.circle_fri.normalized_line_arity4_prepared_polynomial_refs
          values alphaPowers inverses = ok out ∧
      canonicalQM31 out ∧
      qm31View out =
        AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
          (m31View inverses.val[0]!) (m31View inverses.val[1]!)
          (m31View inverses.val[2]!)
          (fun i => qm31View values.val[i.val]!) := by
  rcases normalized_candidate_corresponds values alphaPowers inverses alpha
      hValues hInverses hAlphaPowers with ⟨out, hRun, hCanonical, hExact⟩
  exact ⟨out, by
    simpa [V5FriArithmeticExact.circle_fri.normalized_line_arity4_prepared_polynomial_refs]
      using hRun, hCanonical, hExact⟩

/-- The extracted circle-to-line wrapper uses the exact deployed twiddle
order `(inv2y, -inv2y, inv2x)`, so its successful result is the maintained
circle fold. -/
theorem normalized_circle_to_line_corresponds
    (values : Array Fresh.QM31 4#usize)
    (alphaPowers : Array Fresh.Prepared 3#usize)
    (inv2x inv2y : Fresh.M31)
    (alpha : ExactQM31)
    (hValues : CanonicalQM31Array4 values)
    (hInv2x : canonicalM31 inv2x)
    (hInv2y : canonicalM31 inv2y)
    (hAlphaPowers : PreparedArrayRepresents alphaPowers
      (fun i => alpha ^ (i + 1))) :
    ∃ out : Fresh.QM31,
      V5FriArithmeticExact.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
          values alphaPowers inv2x inv2y = ok out ∧
      canonicalQM31 out ∧
      qm31View out =
        AspisV5ComponentCConcreteFoldLinearity.circleFoldValue alpha
          (m31View inv2x) (m31View inv2y)
          (fun i => qm31View values.val[i.val]!) := by
  rcases m31_neg_corresponds inv2y hInv2y with
    ⟨negInv2y, hNeg, hNegCanonical, hNegExact⟩
  let inverses : Array Fresh.M31 3#usize :=
    Array.make 3#usize [inv2y, negInv2y, inv2x]
  have hInverses : CanonicalM31Array3 inverses := by
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases hCases with rfl | rfl | rfl
    all_goals simp only [inverses, Aeneas.Std.Array.make]
    all_goals assumption
  rcases normalized_candidate_corresponds values alphaPowers inverses alpha
      hValues hInverses hAlphaPowers with ⟨out, hRun, hCanonical, hExact⟩
  refine ⟨out, ?_, hCanonical, ?_⟩
  · unfold
      V5FriArithmeticExact.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
    rw [hNeg]
    simpa only [bind_tc_ok, inverses]
  · rw [hExact]
    unfold AspisV5ComponentCConcreteFoldLinearity.circleFoldValue
    have hNegView : m31View negInv2y = -(m31View inv2y) := by
      apply QuadraticAlgebra.ext
      · apply QuadraticAlgebra.ext
        · exact hNegExact
        · simp [m31View]
      · simp [m31View]
    norm_num [inverses, Aeneas.Std.Array.make]
    rw [hNegView]

private theorem fresh_one_eq : V5FriArithmeticExact.field.M31.ONE = 1#u32 := by
  unfold V5FriArithmeticExact.field.M31.ONE
  rfl

private theorem fresh_one_canonical :
    canonicalM31 V5FriArithmeticExact.field.M31.ONE := by
  rw [fresh_one_eq]
  norm_num [canonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem fresh_one_exact :
    ((V5FriArithmeticExact.field.M31.ONE.val : Nat) : ExactM31) = 1 := by
  rw [fresh_one_eq]
  norm_num

/-- `double_x` computes the exact natural-line coordinate `2*x^2-1`. -/
theorem double_x_corresponds
    (x : Fresh.M31) (hx : canonicalM31 x) :
    ∃ out : Fresh.M31,
      V5FriArithmeticExact.circle_fri.double_x x = ok out ∧
      canonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        2 * ((x.val : Nat) : ExactM31) ^ 2 - 1 := by
  rcases m31_mul_corresponds x x hx hx with
    ⟨square, hSquare, hSquareCanonical, hSquareExact⟩
  rcases m31_double_corresponds square hSquareCanonical with
    ⟨twiceSquare, hTwiceSquare, hTwiceSquareCanonical, hTwiceSquareExact⟩
  rcases m31_sub_corresponds twiceSquare
      V5FriArithmeticExact.field.M31.ONE hTwiceSquareCanonical
      fresh_one_canonical with
    ⟨out, hOut, hOutCanonical, hOutExact⟩
  refine ⟨out, ?_, hOutCanonical, ?_⟩
  · simp [V5FriArithmeticExact.circle_fri.double_x, hSquare,
      hTwiceSquare, hOut]
  · rw [hOutExact, hTwiceSquareExact, hSquareExact, fresh_one_exact]
    ring

private def liftM31U64 (x : Fresh.M31) : Std.U64 :=
  core.convert.num.FromU64U32.from x

private def lazyProduct (left right : Fresh.M31) : Std.U64 :=
  Std.U64.wrapping_mul (liftM31U64 left) (liftM31U64 right)

private def lazyDot3Accumulator
    (a b c x y z : Fresh.M31) : Std.U64 :=
  Std.U64.wrapping_add
    (Std.U64.wrapping_add (lazyProduct a x) (lazyProduct b y))
    (lazyProduct c z)

@[simp] private theorem liftM31U64_val (x : Fresh.M31) :
    (liftM31U64 x).val = x.val := by
  simp [liftM31U64, core.convert.num.FromU64U32.from_val_eq]

private theorem u64_wrapping_mul_exact (left right : Std.U64)
    (hBound : left.val * right.val < 2 ^ 64) :
    (Std.U64.wrapping_mul left right).val = left.val * right.val := by
  rw [Std.U64.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hBound

private theorem u64_wrapping_add_exact (left right : Std.U64)
    (hBound : left.val + right.val < 2 ^ 64) :
    (Std.U64.wrapping_add left right).val = left.val + right.val := by
  rw [Std.U64.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hBound

private theorem canonical_product_le
    (left right : Fresh.M31)
    (hLeft : canonicalM31 left) (hRight : canonicalM31 right) :
    left.val * right.val ≤ (2147483647 - 1) ^ 2 := by
  have hLeftLe : left.val ≤ 2147483647 - 1 := Nat.le_pred_of_lt hLeft
  have hRightLe : right.val ≤ 2147483647 - 1 := Nat.le_pred_of_lt hRight
  simpa [pow_two] using Nat.mul_le_mul hLeftLe hRightLe

private theorem lazy_product_val
    (left right : Fresh.M31)
    (hLeft : canonicalM31 left) (hRight : canonicalM31 right) :
    (lazyProduct left right).val = left.val * right.val := by
  unfold lazyProduct
  rw [u64_wrapping_mul_exact]
  · simp
  · calc
      (liftM31U64 left).val * (liftM31U64 right).val =
          left.val * right.val := by simp
      _ ≤ (2147483647 - 1) ^ 2 :=
        canonical_product_le left right hLeft hRight
      _ < 2 ^ 64 := by norm_num

/-- The terminal evaluator's three lazy M31 products and two additions do
not wrap `u64`; its accumulator is their ordinary natural-number sum. -/
theorem lazy_dot3_accumulator_exact
    (a b c x y z : Fresh.M31)
    (ha : canonicalM31 a) (hb : canonicalM31 b)
    (hc : canonicalM31 c) (hx : canonicalM31 x)
    (hy : canonicalM31 y) (hz : canonicalM31 z) :
    (lazyDot3Accumulator a b c x y z).val =
      a.val * x.val + b.val * y.val + c.val * z.val := by
  have hAX := lazy_product_val a x ha hx
  have hBY := lazy_product_val b y hb hy
  have hCZ := lazy_product_val c z hc hz
  have hAXLe := canonical_product_le a x ha hx
  have hBYLe := canonical_product_le b y hb hy
  have hCZLe := canonical_product_le c z hc hz
  have hFirstBound :
      (lazyProduct a x).val + (lazyProduct b y).val < 2 ^ 64 := by
    rw [hAX, hBY]
    calc
      a.val * x.val + b.val * y.val ≤
          2 * (2147483647 - 1) ^ 2 := by omega
      _ < 2 ^ 64 := by norm_num
  have hFirst := u64_wrapping_add_exact (lazyProduct a x)
    (lazyProduct b y) hFirstBound
  have hFinalBound :
      (Std.U64.wrapping_add (lazyProduct a x) (lazyProduct b y)).val +
          (lazyProduct c z).val < 2 ^ 64 := by
    rw [hFirst, hAX, hBY, hCZ]
    calc
      a.val * x.val + b.val * y.val + c.val * z.val ≤
          3 * (2147483647 - 1) ^ 2 := by omega
      _ < 2 ^ 64 := by norm_num
  unfold lazyDot3Accumulator
  rw [u64_wrapping_add_exact _ _ hFinalBound, hFirst, hAX, hBY, hCZ]

/-- One generated terminal-limb closure returns the exact three-term M31
dot product represented by its successful reduction. -/
theorem final_tensor_limb_closure_corresponds
    (x y z a b c : Fresh.M31)
    (hx : canonicalM31 x) (hy : canonicalM31 y)
    (hz : canonicalM31 z) (ha : canonicalM31 a)
    (hb : canonicalM31 b) (hc : canonicalM31 c) :
    ∃ out : Fresh.M31,
      V5FriArithmeticExact.circle_fri.evaluate_final_line_tensor_ref.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
          (x, y, z) (a, b, c) = ok out ∧
      canonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        ((a.val : Nat) : ExactM31) * ((x.val : Nat) : ExactM31) +
        ((b.val : Nat) : ExactM31) * ((y.val : Nat) : ExactM31) +
        ((c.val : Nat) : ExactM31) * ((z.val : Nat) : ExactM31) := by
  let accumulator := lazyDot3Accumulator a b c x y z
  have hAccumulator := lazy_dot3_accumulator_exact a b c x y z
    ha hb hc hx hy hz
  rcases m31_reduce_u64_corresponds accumulator with
    ⟨out, hReduce, hCanonical, hExact⟩
  refine ⟨out, ?_, hCanonical, ?_⟩
  · unfold
      V5FriArithmeticExact.circle_fri.evaluate_final_line_tensor_ref.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
    simp only [Std.lift, bind_tc_ok]
    change V5FriArithmeticExact.field.M31.reduce_u64 accumulator = ok out
    exact hReduce
  · rw [hExact, hAccumulator, Nat.cast_add, Nat.cast_mul,
      Nat.cast_add, Nat.cast_mul, Nat.cast_mul]

/-- Successful execution of the unchanged terminal evaluator returns exactly
the maintained natural final-line tensor on its four QM31 coefficients. -/
theorem evaluate_final_line_tensor_corresponds
    (coefficients : Array Fresh.QM31 4#usize)
    (x : Fresh.M31)
    (hCoefficients : CanonicalQM31Array4 coefficients)
    (hx : canonicalM31 x) :
    ∃ out : Fresh.QM31,
      V5FriArithmeticExact.circle_fri.evaluate_final_line_tensor_ref
          coefficients x = ok out ∧
      canonicalQM31 out ∧
      qm31View out =
        AspisV5ComponentCConcreteFoldLinearity.finalTensorValue
          (m31View x) (fun i => qm31View coefficients.val[i.val]!) := by
  have hc0 := hCoefficients 0 (by norm_num)
  have hc1 := hCoefficients 1 (by norm_num)
  have hc2 := hCoefficients 2 (by norm_num)
  have hc3 := hCoefficients 3 (by norm_num)
  have hq0 := generated_array_index_run coefficients 0#usize (by norm_num)
  have hq1 := generated_array_index_run coefficients 1#usize (by norm_num)
  have hq2 := generated_array_index_run coefficients 2#usize (by norm_num)
  have hq3 := generated_array_index_run coefficients 3#usize (by norm_num)
  rcases double_x_corresponds x hx with
    ⟨piX, hPiX, hPiXCanonical, hPiXExact⟩
  rcases m31_mul_corresponds x piX hx hPiXCanonical with
    ⟨xPiX, hXPiX, hXPiXCanonical, hXPiXExact⟩
  rcases final_tensor_limb_closure_corresponds x piX xPiX
      coefficients.val[1]!.c0.a coefficients.val[2]!.c0.a
      coefficients.val[3]!.c0.a hx hPiXCanonical hXPiXCanonical
      hc1.1.1 hc2.1.1 hc3.1.1 with
    ⟨m0, hm0, hm0Canonical, hm0Exact⟩
  rcases final_tensor_limb_closure_corresponds x piX xPiX
      coefficients.val[1]!.c0.b coefficients.val[2]!.c0.b
      coefficients.val[3]!.c0.b hx hPiXCanonical hXPiXCanonical
      hc1.1.2 hc2.1.2 hc3.1.2 with
    ⟨m1, hm1, hm1Canonical, hm1Exact⟩
  rcases final_tensor_limb_closure_corresponds x piX xPiX
      coefficients.val[1]!.c1.a coefficients.val[2]!.c1.a
      coefficients.val[3]!.c1.a hx hPiXCanonical hXPiXCanonical
      hc1.2.1 hc2.2.1 hc3.2.1 with
    ⟨m2, hm2, hm2Canonical, hm2Exact⟩
  rcases final_tensor_limb_closure_corresponds x piX xPiX
      coefficients.val[1]!.c1.b coefficients.val[2]!.c1.b
      coefficients.val[3]!.c1.b hx hPiXCanonical hXPiXCanonical
      hc1.2.2 hc2.2.2 hc3.2.2 with
    ⟨m3, hm3, hm3Canonical, hm3Exact⟩
  let lazy : Fresh.QM31 := ⟨⟨m0, m1⟩, ⟨m2, m3⟩⟩
  have hLazyCanonical : canonicalQM31 lazy :=
    ⟨⟨hm0Canonical, hm1Canonical⟩, ⟨hm2Canonical, hm3Canonical⟩⟩
  have hLazyExact :
      qm31View lazy =
        qm31View coefficients.val[1]! * m31View x +
        qm31View coefficients.val[2]! * m31View piX +
        qm31View coefficients.val[3]! * m31View xPiX := by
    apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · simpa [lazy, qm31View, cm31View, m31View, m31CMView] using hm0Exact
      · simpa [lazy, qm31View, cm31View, m31View, m31CMView] using hm1Exact
    · apply QuadraticAlgebra.ext
      · simpa [lazy, qm31View, cm31View, m31View, m31CMView] using hm2Exact
      · simpa [lazy, qm31View, cm31View, m31View, m31CMView] using hm3Exact
  rcases qm31_add_corresponds coefficients.val[0]! lazy hc0 hLazyCanonical with
    ⟨out, hOut, hOutCanonical, hOutExact⟩
  have hPiXView :
      m31View piX = 2 * (m31View x) ^ 2 - 1 := by
    rw [m31View_eq_algebraMap piX, m31View_eq_algebraMap x]
    have hMap := congrArg (algebraMap ExactM31 ExactQM31) hPiXExact
    simpa only [map_sub, map_mul, map_pow, map_one, map_ofNat] using hMap
  have hXPiXView : m31View xPiX = m31View x * m31View piX := by
    rw [m31View_eq_algebraMap xPiX, m31View_eq_algebraMap x,
      m31View_eq_algebraMap piX]
    have hMap := congrArg (algebraMap ExactM31 ExactQM31) hXPiXExact
    simpa only [map_mul] using hMap
  refine ⟨out, ?_, hOutCanonical, ?_⟩
  · unfold V5FriArithmeticExact.circle_fri.evaluate_final_line_tensor_ref
    rw [hPiX]
    simp only [bind_tc_ok]
    rw [hXPiX]
    simp only [bind_tc_ok]
    rw [hq0]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hq1]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hq2]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hq3]
    simp only [bind_tc_ok, UScalar.ofNatCore_val_eq]
    rw [hm0]
    simp only [bind_tc_ok]
    rw [hm1]
    simp only [bind_tc_ok]
    rw [hm2]
    simp only [bind_tc_ok]
    rw [hm3]
    simp only [bind_tc_ok]
    change V5FriArithmeticExact.field.QM31.add coefficients.val[0]! lazy = ok out
    exact hOut
  · rw [hOutExact, hLazyExact, hXPiXView, hPiXView]
    unfold AspisV5ComponentCConcreteFoldLinearity.finalTensorValue
    norm_num
    ring


end AspisV5FriFoldSemantics

#print axioms AspisV5FriFoldSemantics.normalized_candidate_corresponds
#print axioms AspisV5FriFoldSemantics.normalized_line_corresponds
#print axioms AspisV5FriFoldSemantics.normalized_circle_to_line_corresponds
#print axioms AspisV5FriFoldSemantics.double_x_corresponds
#print axioms AspisV5FriFoldSemantics.lazy_dot3_accumulator_exact
#print axioms AspisV5FriFoldSemantics.final_tensor_limb_closure_corresponds
#print axioms AspisV5FriFoldSemantics.evaluate_final_line_tensor_corresponds
