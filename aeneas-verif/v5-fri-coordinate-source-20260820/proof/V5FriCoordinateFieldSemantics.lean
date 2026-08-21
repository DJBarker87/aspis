import Coordinates.Funs
import V5FriArithmeticSemantics
import V5FriCoordinateMathematics

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

/-!
# Field and point semantics of the extracted coordinate helper

The coordinate extraction and the earlier FRI arithmetic extraction contain
separate generated copies of the same unchanged M31 methods.  This file proves
literal call equality between those copies and reuses the already checked M31
semantics.  The resulting theorems describe successful source calls; no output
coordinate or inverse-table postcondition is assumed.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCoordinateFieldSemantics

namespace Coordinate
open V5FriCoordinateAdapter

abbrev M31 := aspis_core.field.M31
abbrev Point := aspis_core.circle_fri.BaseCirclePoint

end Coordinate

namespace Arithmetic
open V5FriArithmeticExact

abbrev M31 := field.M31

end Arithmetic

open AspisV5FriArithmeticSemantics
open AspisV5FriCoordinateMathematics
open AspisCircleGroupOrder

def canonicalM31 (value : Coordinate.M31) : Prop :=
  AspisV5FriArithmeticSemantics.canonicalM31 value

def m31Value (value : Coordinate.M31) : ZMod P := value.val

def pointValue (point : Coordinate.Point) : ZMod P × ZMod P :=
  (m31Value point.x, m31Value point.y)

def pointCanonical (point : Coordinate.Point) : Prop :=
  canonicalM31 point.x ∧ canonicalM31 point.y

/-- Canonical raw M31 words are uniquely determined by their field value. -/
theorem canonical_eq_of_m31Value_eq
    (left right : Coordinate.M31)
    (hleft : canonicalM31 left) (hright : canonicalM31 right)
    (hvalue : m31Value left = m31Value right) : left = right := by
  apply UScalar.eq_of_val_eq
  have hleftLt : left.val < P := by
    exact hleft
  have hrightLt : right.val < P := by
    exact hright
  have hvals := congrArg ZMod.val hvalue
  simpa [m31Value, ZMod.val_natCast_of_lt hleftLt,
    ZMod.val_natCast_of_lt hrightLt] using hvals

private theorem coordinate_P_eq_arithmetic :
    V5FriCoordinateAdapter.aspis_core.field.P =
      V5FriArithmeticExact.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5FriCoordinateAdapter.aspis_core.field.P
    V5FriArithmeticExact.field.P
  rfl

private theorem coordinate_reduce_call_eq_arithmetic (value : Std.U64) :
    V5FriCoordinateAdapter.aspis_core.field.reduce_u64 value =
      V5FriArithmeticExact.field.reduce_u64 value := by
  unfold V5FriCoordinateAdapter.aspis_core.field.reduce_u64
    V5FriArithmeticExact.field.reduce_u64
  rw [coordinate_P_eq_arithmetic]

private theorem coordinate_mul_call_eq_arithmetic
    (left right : Coordinate.M31) :
    V5FriCoordinateAdapter.aspis_core.field.M31.mul left right =
      V5FriArithmeticExact.field.M31.mul left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.mul
    V5FriArithmeticExact.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [coordinate_reduce_call_eq_arithmetic]

private theorem coordinate_add_call_eq_arithmetic
    (left right : Coordinate.M31) :
    V5FriCoordinateAdapter.aspis_core.field.M31.add left right =
      V5FriArithmeticExact.field.M31.add left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.add
    V5FriArithmeticExact.field.M31.add
  rw [coordinate_P_eq_arithmetic]

private theorem coordinate_sub_call_eq_arithmetic
    (left right : Coordinate.M31) :
    V5FriCoordinateAdapter.aspis_core.field.M31.sub left right =
      V5FriArithmeticExact.field.M31.sub left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.sub
    V5FriArithmeticExact.field.M31.sub
  rw [coordinate_P_eq_arithmetic]

private theorem coordinate_neg_call_eq_arithmetic (value : Coordinate.M31) :
    V5FriCoordinateAdapter.aspis_core.field.M31.neg value =
      V5FriArithmeticExact.field.M31.neg value := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.neg
    V5FriArithmeticExact.field.M31.neg
  rw [coordinate_P_eq_arithmetic]

theorem add_corresponds
    (left right output : Coordinate.M31)
    (hleft : canonicalM31 left) (hright : canonicalM31 right)
    (hcall : V5FriCoordinateAdapter.aspis_core.field.M31.add left right =
      .ok output) :
    canonicalM31 output ∧
      m31Value output = m31Value left + m31Value right := by
  have hexact : V5FriArithmeticExact.field.M31.add left right = .ok output := by
    rw [← coordinate_add_call_eq_arithmetic]
    exact hcall
  obtain ⟨result, hresult, hcanonical, hvalue⟩ :=
    m31_add_corresponds left right hleft hright
  rw [hexact] at hresult
  have : result = output := Result.ok.inj hresult.symm
  subst result
  exact ⟨hcanonical, hvalue⟩

theorem sub_corresponds
    (left right output : Coordinate.M31)
    (hleft : canonicalM31 left) (hright : canonicalM31 right)
    (hcall : V5FriCoordinateAdapter.aspis_core.field.M31.sub left right =
      .ok output) :
    canonicalM31 output ∧
      m31Value output = m31Value left - m31Value right := by
  have hexact : V5FriArithmeticExact.field.M31.sub left right = .ok output := by
    rw [← coordinate_sub_call_eq_arithmetic]
    exact hcall
  obtain ⟨result, hresult, hcanonical, hvalue⟩ :=
    m31_sub_corresponds left right hleft hright
  rw [hexact] at hresult
  have : result = output := Result.ok.inj hresult.symm
  subst result
  exact ⟨hcanonical, hvalue⟩

theorem mul_corresponds
    (left right output : Coordinate.M31)
    (hleft : canonicalM31 left) (hright : canonicalM31 right)
    (hcall : V5FriCoordinateAdapter.aspis_core.field.M31.mul left right =
      .ok output) :
    canonicalM31 output ∧
      m31Value output = m31Value left * m31Value right := by
  have hexact : V5FriArithmeticExact.field.M31.mul left right = .ok output := by
    rw [← coordinate_mul_call_eq_arithmetic]
    exact hcall
  obtain ⟨result, hresult, hcanonical, hvalue⟩ :=
    m31_mul_corresponds left right hleft hright
  rw [hexact] at hresult
  have : result = output := Result.ok.inj hresult.symm
  subst result
  exact ⟨hcanonical, hvalue⟩

theorem neg_corresponds
    (input output : Coordinate.M31)
    (hinput : canonicalM31 input)
    (hcall : V5FriCoordinateAdapter.aspis_core.field.M31.neg input =
      .ok output) :
    canonicalM31 output ∧ m31Value output = -m31Value input := by
  have hexact : V5FriArithmeticExact.field.M31.neg input = .ok output := by
    rw [← coordinate_neg_call_eq_arithmetic]
    exact hcall
  obtain ⟨result, hresult, hcanonical, hvalue⟩ :=
    m31_neg_corresponds input hinput
  rw [hexact] at hresult
  have : result = output := Result.ok.inj hresult.symm
  subst result
  exact ⟨hcanonical, hvalue⟩

theorem double_corresponds
    (input output : Coordinate.M31)
    (hinput : canonicalM31 input)
    (hcall : V5FriCoordinateAdapter.aspis_core.field.M31.double input =
      .ok output) :
    canonicalM31 output ∧ m31Value output = 2 * m31Value input := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.double at hcall
  have h := add_corresponds input input output hinput hinput hcall
  exact ⟨h.1, by simpa [two_mul] using h.2⟩

/-- A successful extracted point addition implements the circle group law. -/
theorem point_add_corresponds
    (left right output : Coordinate.Point)
    (hleft : pointCanonical left) (hright : pointCanonical right)
    (hcall :
      V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint.add
        left right = .ok output) :
    pointCanonical output ∧
      pointValue output =
        (m31Value left.x * m31Value right.x -
            m31Value left.y * m31Value right.y,
          m31Value left.x * m31Value right.y +
            m31Value left.y * m31Value right.x) := by
  unfold V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint.add at hcall
  generalize hxxCall :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left.x right.x = xxResult
      at hcall
  cases xxResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hcall
  | div => simp [Bind.bind, Aeneas.Std.bind] at hcall
  | ok xx =>
    generalize hyyCall :
        V5FriCoordinateAdapter.aspis_core.field.M31.mul left.y right.y = yyResult
        at hcall
    cases yyResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hcall
    | div => simp [Bind.bind, Aeneas.Std.bind] at hcall
    | ok yy =>
      generalize hxCall :
          V5FriCoordinateAdapter.aspis_core.field.M31.sub xx yy = xResult
          at hcall
      cases xResult with
      | fail error => simp [hxCall] at hcall
      | div => simp [hxCall] at hcall
      | ok x =>
        generalize hxyCall :
            V5FriCoordinateAdapter.aspis_core.field.M31.mul left.x right.y =
              xyResult at hcall
        cases xyResult with
        | fail error => simp [hxCall, hxyCall] at hcall
        | div => simp [hxCall, hxyCall] at hcall
        | ok xy =>
          generalize hyxCall :
              V5FriCoordinateAdapter.aspis_core.field.M31.mul left.y right.x =
                yxResult at hcall
          cases yxResult with
          | fail error => simp [hxCall, hxyCall, hyxCall] at hcall
          | div => simp [hxCall, hxyCall, hyxCall] at hcall
          | ok yx =>
            generalize hyCall :
                V5FriCoordinateAdapter.aspis_core.field.M31.add xy yx =
                  yResult at hcall
            cases yResult with
            | fail error => simp [hxCall, hxyCall, hyxCall, hyCall] at hcall
            | div => simp [hxCall, hxyCall, hyxCall, hyCall] at hcall
            | ok y =>
              have hxx := mul_corresponds left.x right.x xx hleft.1 hright.1
                hxxCall
              have hyy := mul_corresponds left.y right.y yy hleft.2 hright.2
                hyyCall
              have hx := sub_corresponds xx yy x hxx.1 hyy.1 hxCall
              have hxy := mul_corresponds left.x right.y xy hleft.1 hright.2
                hxyCall
              have hyx := mul_corresponds left.y right.x yx hleft.2 hright.1
                hyxCall
              have hy := add_corresponds xy yx y hxy.1 hyx.1 hyCall
              simp [hxCall, hxyCall, hyxCall, hyCall] at hcall
              have houtput : output = { x := x, y := y } := hcall.symm
              subst output
              exact ⟨⟨hx.1, hy.1⟩, by
                apply Prod.ext
                · simpa [pointValue, hxx.2, hyy.2] using hx.2
                · simpa [pointValue, hxy.2, hyx.2] using hy.2⟩

/-- The optimized extracted point doubling is exact circle squaring. -/
theorem double_point_corresponds
    (input output : Coordinate.Point)
    (hinput : pointCanonical input)
    (hcall : V5FriCoordinateAdapter.aspis_core.circle_fri.double_point input =
      .ok output) :
    pointCanonical output ∧
      pointValue output =
        (m31Value input.x ^ 2 - m31Value input.y ^ 2,
          2 * m31Value input.x * m31Value input.y) := by
  unfold V5FriCoordinateAdapter.aspis_core.circle_fri.double_point at hcall
  generalize haddCall :
      V5FriCoordinateAdapter.aspis_core.field.M31.add input.x input.y =
        addResult at hcall
  cases addResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hcall
  | div => simp [Bind.bind, Aeneas.Std.bind] at hcall
  | ok added =>
    generalize hsubCall :
        V5FriCoordinateAdapter.aspis_core.field.M31.sub input.x input.y =
          subResult at hcall
    cases subResult with
    | fail error => simp [hsubCall] at hcall
    | div => simp [hsubCall] at hcall
    | ok subtracted =>
      generalize hxCall :
          V5FriCoordinateAdapter.aspis_core.field.M31.mul added subtracted =
            xResult at hcall
      cases xResult with
      | fail error => simp [hxCall] at hcall
      | div => simp [hxCall] at hcall
      | ok x =>
        generalize hxyCall :
            V5FriCoordinateAdapter.aspis_core.field.M31.mul input.x input.y =
              xyResult at hcall
        cases xyResult with
        | fail error => simp [hxCall, hxyCall] at hcall
        | div => simp [hxCall, hxyCall] at hcall
        | ok xy =>
          generalize hyCall :
              V5FriCoordinateAdapter.aspis_core.field.M31.double xy = yResult
              at hcall
          cases yResult with
          | fail error => simp [hxCall, hxyCall, hyCall] at hcall
          | div => simp [hxCall, hxyCall, hyCall] at hcall
          | ok y =>
            have hadd := add_corresponds input.x input.y added hinput.1 hinput.2
              haddCall
            have hsub := sub_corresponds input.x input.y subtracted hinput.1
              hinput.2 hsubCall
            have hx := mul_corresponds added subtracted x hadd.1 hsub.1 hxCall
            have hxy := mul_corresponds input.x input.y xy hinput.1 hinput.2
              hxyCall
            have hy := double_corresponds xy y hxy.1 hyCall
            simp [hxCall, hxyCall, hyCall] at hcall
            have houtput : output = { x := x, y := y } := hcall.symm
            subst output
            refine ⟨⟨hx.1, hy.1⟩, ?_⟩
            apply Prod.ext
            · change m31Value x =
                m31Value input.x ^ 2 - m31Value input.y ^ 2
              rw [hx.2, hadd.2, hsub.2]
              ring
            · change m31Value y =
                2 * m31Value input.x * m31Value input.y
              rw [hy.2, hxy.2]
              ring

/-! ## The inversion backend used by the batch routine -/

/-- The extracted repeated-squaring loop has its ordinary field meaning. -/
theorem square_n_loop_corresponds
    (remaining : Nat)
    (iter : core.ops.range.Range Std.Usize)
    (hspan : iter.start.val + remaining = iter.end.val)
    (value : Coordinate.M31) (hvalue : canonicalM31 value) :
    ∃ output : Coordinate.M31,
      V5FriCoordinateAdapter.aspis_core.field.square_n_loop iter value =
        .ok output ∧
      canonicalM31 output ∧
      m31Value output = m31Value value ^ (2 ^ remaining) := by
  induction remaining generalizing iter value with
  | zero =>
      have hge : iter.start.val ≥ iter.end.val := by omega
      have hnextSpec :=
        core.iter.range.IteratorRange.next_Usize_none_spec iter hge
      obtain ⟨⟨nextValue, iterNext⟩, hnext, hnone, hiter⟩ :=
        Aeneas.Std.WP.spec_imp_exists hnextSpec
      rw [hnone, hiter] at hnext
      refine ⟨value, ?_, hvalue, by simp⟩
      unfold V5FriCoordinateAdapter.aspis_core.field.square_n_loop
      rw [loop.eq_def]
      unfold V5FriCoordinateAdapter.aspis_core.field.square_n_loop.body
      simp only
      rw [hnext]
      rfl
  | succ count ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hnextSpec :=
        core.iter.range.IteratorRange.next_Usize_some_spec iter hlt
      obtain ⟨⟨nextValue, iterNext⟩, hnext, hsome, hstart, hend⟩ :=
        Aeneas.Std.WP.spec_imp_exists hnextSpec
      rw [hsome] at hnext
      obtain ⟨squared, hsquaredArithmeticRun, hsquaredCanonical,
          hsquaredValue⟩ :=
        m31_mul_corresponds value value hvalue hvalue
      have hsquaredRun :
          V5FriCoordinateAdapter.aspis_core.field.M31.mul value value =
            .ok squared := by
        rw [coordinate_mul_call_eq_arithmetic]
        exact hsquaredArithmeticRun
      have hspanNext :
          iterNext.start.val + count = iterNext.end.val := by
        rw [hend, hstart]
        omega
      obtain ⟨output, hloop, houtputCanonical, houtputValue⟩ :=
        ih iterNext hspanNext squared hsquaredCanonical
      refine ⟨output, ?_, houtputCanonical, ?_⟩
      · unfold V5FriCoordinateAdapter.aspis_core.field.square_n_loop
        rw [loop.eq_def]
        unfold V5FriCoordinateAdapter.aspis_core.field.square_n_loop.body
        simp only
        rw [hnext]
        simp only [bind_tc_ok]
        rw [hsquaredRun]
        simp only [bind_tc_ok]
        change
          V5FriCoordinateAdapter.aspis_core.field.square_n_loop
              iterNext squared = .ok output
        exact hloop
      · change m31Value squared =
          m31Value value * m31Value value at hsquaredValue
        rw [houtputValue, hsquaredValue, ← pow_two, ← pow_mul]
        congr 1
        simp [pow_succ, Nat.mul_comm]

/-- Wrapper form of `square_n_loop_corresponds`. -/
theorem square_n_corresponds
    (value : Coordinate.M31) (hvalue : canonicalM31 value)
    (count : Std.Usize) :
    ∃ output : Coordinate.M31,
      V5FriCoordinateAdapter.aspis_core.field.square_n value count =
        .ok output ∧
      canonicalM31 output ∧
      m31Value output = m31Value value ^ (2 ^ count.val) := by
  exact square_n_loop_corresponds count.val
    { start := 0#usize, «end» := count } (by simp) value hvalue

/-- Constructive form of the extracted multiplication theorem. -/
theorem mul_produces_canonical
    (left right : Coordinate.M31)
    (hleft : canonicalM31 left) (hright : canonicalM31 right) :
    ∃ output : Coordinate.M31,
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left right =
        .ok output ∧
      canonicalM31 output ∧
      m31Value output = m31Value left * m31Value right := by
  obtain ⟨output, hrun, hcanonical, hvalue⟩ :=
    m31_mul_corresponds left right hleft hright
  refine ⟨output, ?_, hcanonical, hvalue⟩
  rw [coordinate_mul_call_eq_arithmetic]
  exact hrun

/-- Constructive form of the extracted doubling theorem. -/
theorem double_produces_canonical
    (input : Coordinate.M31) (hinput : canonicalM31 input) :
    ∃ output : Coordinate.M31,
      V5FriCoordinateAdapter.aspis_core.field.M31.double input =
        .ok output ∧
      canonicalM31 output ∧
      m31Value output = 2 * m31Value input := by
  obtain ⟨output, hrunArithmetic, hcanonical, hvalue⟩ :=
    m31_add_corresponds input input hinput hinput
  have hrun :
      V5FriCoordinateAdapter.aspis_core.field.M31.add input input =
        .ok output := by
    rw [coordinate_add_call_eq_arithmetic]
    exact hrunArithmetic
  refine ⟨output, ?_, hcanonical, ?_⟩
  · unfold V5FriCoordinateAdapter.aspis_core.field.M31.double
    exact hrun
  · have hvalue' :
        m31Value output = m31Value input + m31Value input := by
      simpa [m31Value] using hvalue
    rw [hvalue']
    ring

/-- The source zero test returns false whenever the represented field value
is nonzero. -/
theorem is_zero_false
    (input : Coordinate.M31) (hnonzero : m31Value input ≠ 0) :
    V5FriCoordinateAdapter.aspis_core.field.M31.is_zero input = .ok false := by
  have hraw : input ≠ 0#u32 := by
    intro heq
    apply hnonzero
    subst input
    rfl
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.is_zero
  simp [hraw]

/-- The extracted helper used for the final FRI x-coordinate computes
`2*x^2 - 1` in the base field. -/
theorem double_x_produces_canonical
    (input : Coordinate.M31) (hinput : canonicalM31 input) :
    ∃ output : Coordinate.M31,
      V5FriCoordinateAdapter.aspis_core.circle_fri.double_x input =
        .ok output ∧
      canonicalM31 output ∧
      m31Value output = 2 * m31Value input ^ 2 - 1 := by
  obtain ⟨squared, hsquaredRun, hsquaredCanonical, hsquaredValue⟩ :=
    mul_produces_canonical input input hinput hinput
  obtain ⟨doubled, hdoubledArithmeticRun, hdoubledCanonical,
      hdoubledValue⟩ :=
    m31_add_corresponds squared squared hsquaredCanonical hsquaredCanonical
  have hdoubledRun :
      V5FriCoordinateAdapter.aspis_core.field.M31.add squared squared =
        .ok doubled := by
    rw [coordinate_add_call_eq_arithmetic]
    exact hdoubledArithmeticRun
  have honeCanonical :
      canonicalM31 V5FriCoordinateAdapter.aspis_core.field.M31.ONE := by
    norm_num [canonicalM31, AspisV5FriArithmeticSemantics.canonicalM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      V5FriCoordinateAdapter.aspis_core.field.M31.ONE]
  obtain ⟨output, houtputArithmeticRun, houtputCanonical, houtputValue⟩ :=
    m31_sub_corresponds doubled
      V5FriCoordinateAdapter.aspis_core.field.M31.ONE
      hdoubledCanonical honeCanonical
  have houtputRun :
      V5FriCoordinateAdapter.aspis_core.field.M31.sub doubled
          V5FriCoordinateAdapter.aspis_core.field.M31.ONE = .ok output := by
    rw [coordinate_sub_call_eq_arithmetic]
    exact houtputArithmeticRun
  refine ⟨output, ?_, houtputCanonical, ?_⟩
  · unfold V5FriCoordinateAdapter.aspis_core.circle_fri.double_x
      V5FriCoordinateAdapter.aspis_core.field.M31.double
    simp only [hsquaredRun, bind_tc_ok, hdoubledRun, houtputRun]
  · have houtputValue' :
        m31Value output = m31Value doubled - 1 := by
      simpa [m31Value, V5FriCoordinateAdapter.aspis_core.field.M31.ONE]
        using houtputValue
    have hdoubledValue' :
        m31Value doubled = m31Value squared + m31Value squared := by
      simpa [m31Value] using hdoubledValue
    rw [houtputValue', hdoubledValue', hsquaredValue]
    ring

/-- A successful call to the exact extracted inversion backend returns a
canonical M31 value.  Its mathematical inverse property is deliberately not
needed by the batch proof: the production code validates the common backend
factor with its first denominator/output product. -/
theorem inv_output_canonical
    (input output : Coordinate.M31)
    (hinput : canonicalM31 input) (hnonzero : input.val ≠ 0)
    (hcall : V5FriCoordinateAdapter.aspis_core.field.M31.inv input =
      .ok output) :
    canonicalM31 output := by
  obtain ⟨x2, hx2Run, hx2Canonical, _⟩ :=
    mul_produces_canonical input input hinput hinput
  obtain ⟨t2, ht2Run, ht2Canonical, _⟩ :=
    mul_produces_canonical x2 input hx2Canonical hinput
  obtain ⟨t2Squared2, ht2Squared2Run, ht2Squared2Canonical, _⟩ :=
    square_n_corresponds t2 ht2Canonical 2#usize
  obtain ⟨t4, ht4Run, ht4Canonical, _⟩ :=
    mul_produces_canonical t2Squared2 t2 ht2Squared2Canonical ht2Canonical
  obtain ⟨t4Squared4, ht4Squared4Run, ht4Squared4Canonical, _⟩ :=
    square_n_corresponds t4 ht4Canonical 4#usize
  obtain ⟨t8, ht8Run, ht8Canonical, _⟩ :=
    mul_produces_canonical t4Squared4 t4 ht4Squared4Canonical ht4Canonical
  obtain ⟨t8Squared8, ht8Squared8Run, ht8Squared8Canonical, _⟩ :=
    square_n_corresponds t8 ht8Canonical 8#usize
  obtain ⟨t16, ht16Run, ht16Canonical, _⟩ :=
    mul_produces_canonical t8Squared8 t8 ht8Squared8Canonical ht8Canonical
  obtain ⟨t16Squared8, ht16Squared8Run, ht16Squared8Canonical, _⟩ :=
    square_n_corresponds t16 ht16Canonical 8#usize
  obtain ⟨t24, ht24Run, ht24Canonical, _⟩ :=
    mul_produces_canonical t16Squared8 t8 ht16Squared8Canonical ht8Canonical
  obtain ⟨t24Squared4, ht24Squared4Run, ht24Squared4Canonical, _⟩ :=
    square_n_corresponds t24 ht24Canonical 4#usize
  obtain ⟨t28, ht28Run, ht28Canonical, _⟩ :=
    mul_produces_canonical t24Squared4 t4 ht24Squared4Canonical ht4Canonical
  obtain ⟨t28Squared, ht28SquaredRun, ht28SquaredCanonical, _⟩ :=
    mul_produces_canonical t28 t28 ht28Canonical ht28Canonical
  obtain ⟨t29, ht29Run, ht29Canonical, _⟩ :=
    mul_produces_canonical t28Squared input ht28SquaredCanonical hinput
  obtain ⟨t30, ht30Run, ht30Canonical, _⟩ :=
    mul_produces_canonical t29 t29 ht29Canonical ht29Canonical
  obtain ⟨t30Squared, ht30SquaredRun, ht30SquaredCanonical, _⟩ :=
    mul_produces_canonical t30 t30 ht30Canonical ht30Canonical
  obtain ⟨expected, hexpectedRun, hexpectedCanonical, _⟩ :=
    mul_produces_canonical t30Squared input ht30SquaredCanonical hinput
  have hinputNe : input ≠ 0#u32 := by
    intro heq
    apply hnonzero
    exact congrArg UScalar.val heq
  have hassert : massert (input != 0#u32) = .ok () :=
    (Aeneas.Std.massert_ok _).2 (bne_iff_ne.mpr hinputNe)
  have hexpected :
      V5FriCoordinateAdapter.aspis_core.field.M31.inv input =
        .ok expected := by
    simp only [V5FriCoordinateAdapter.aspis_core.field.M31.inv, hassert,
      bind_tc_ok, hx2Run, ht2Run, ht2Squared2Run, ht4Run,
      ht4Squared4Run, ht8Run, ht8Squared8Run, ht16Run,
      ht16Squared8Run, ht24Run, ht24Squared4Run, ht28Run,
      ht28SquaredRun, ht29Run, ht30Run, ht30SquaredRun, hexpectedRun]
  rw [hexpected] at hcall
  have : expected = output := Result.ok.inj hcall
  subst output
  exact hexpectedCanonical

/-- The translated nonzero inversion call terminates and returns the exact
field inverse.  Its addition-chain value is identified with the maintained
Lean proof of the same production schedule. -/
theorem inv_produces_exact
    (input : Coordinate.M31)
    (hinput : canonicalM31 input) (hnonzero : input.val ≠ 0) :
    ∃ output : Coordinate.M31,
      V5FriCoordinateAdapter.aspis_core.field.M31.inv input = .ok output ∧
      canonicalM31 output ∧
      m31Value output = (m31Value input)⁻¹ := by
  obtain ⟨x2, hx2Run, hx2Canonical, hx2Value⟩ :=
    mul_produces_canonical input input hinput hinput
  obtain ⟨t2, ht2Run, ht2Canonical, ht2Value⟩ :=
    mul_produces_canonical x2 input hx2Canonical hinput
  obtain ⟨t2Squared2, ht2Squared2Run, ht2Squared2Canonical,
      ht2Squared2Value⟩ := square_n_corresponds t2 ht2Canonical 2#usize
  obtain ⟨t4, ht4Run, ht4Canonical, ht4Value⟩ :=
    mul_produces_canonical t2Squared2 t2 ht2Squared2Canonical ht2Canonical
  obtain ⟨t4Squared4, ht4Squared4Run, ht4Squared4Canonical,
      ht4Squared4Value⟩ := square_n_corresponds t4 ht4Canonical 4#usize
  obtain ⟨t8, ht8Run, ht8Canonical, ht8Value⟩ :=
    mul_produces_canonical t4Squared4 t4 ht4Squared4Canonical ht4Canonical
  obtain ⟨t8Squared8, ht8Squared8Run, ht8Squared8Canonical,
      ht8Squared8Value⟩ := square_n_corresponds t8 ht8Canonical 8#usize
  obtain ⟨t16, ht16Run, ht16Canonical, ht16Value⟩ :=
    mul_produces_canonical t8Squared8 t8 ht8Squared8Canonical ht8Canonical
  obtain ⟨t16Squared8, ht16Squared8Run, ht16Squared8Canonical,
      ht16Squared8Value⟩ := square_n_corresponds t16 ht16Canonical 8#usize
  obtain ⟨t24, ht24Run, ht24Canonical, ht24Value⟩ :=
    mul_produces_canonical t16Squared8 t8 ht16Squared8Canonical ht8Canonical
  obtain ⟨t24Squared4, ht24Squared4Run, ht24Squared4Canonical,
      ht24Squared4Value⟩ := square_n_corresponds t24 ht24Canonical 4#usize
  obtain ⟨t28, ht28Run, ht28Canonical, ht28Value⟩ :=
    mul_produces_canonical t24Squared4 t4 ht24Squared4Canonical ht4Canonical
  obtain ⟨t28Squared, ht28SquaredRun, ht28SquaredCanonical,
      ht28SquaredValue⟩ :=
    mul_produces_canonical t28 t28 ht28Canonical ht28Canonical
  obtain ⟨t29, ht29Run, ht29Canonical, ht29Value⟩ :=
    mul_produces_canonical t28Squared input ht28SquaredCanonical hinput
  obtain ⟨t30, ht30Run, ht30Canonical, ht30Value⟩ :=
    mul_produces_canonical t29 t29 ht29Canonical ht29Canonical
  obtain ⟨t30Squared, ht30SquaredRun, ht30SquaredCanonical,
      ht30SquaredValue⟩ :=
    mul_produces_canonical t30 t30 ht30Canonical ht30Canonical
  obtain ⟨output, houtputRun, houtputCanonical, houtputValue⟩ :=
    mul_produces_canonical t30Squared input ht30SquaredCanonical hinput
  have hinputNe : input ≠ 0#u32 := by
    intro heq
    apply hnonzero
    exact congrArg UScalar.val heq
  have hassert : massert (input != 0#u32) = .ok () :=
    (Aeneas.Std.massert_ok _).2 (bne_iff_ne.mpr hinputNe)
  have hrun :
      V5FriCoordinateAdapter.aspis_core.field.M31.inv input =
        .ok output := by
    simp only [V5FriCoordinateAdapter.aspis_core.field.M31.inv, hassert,
      bind_tc_ok, hx2Run, ht2Run, ht2Squared2Run, ht4Run,
      ht4Squared4Run, ht8Run, ht8Squared8Run, ht16Run,
      ht16Squared8Run, ht24Run, ht24Squared4Run, ht28Run,
      ht28SquaredRun, ht29Run, ht30Run, ht30SquaredRun, houtputRun]
  let x := m31Value input
  have hx2Pow : m31Value x2 = x ^ 2 := by
    rw [hx2Value]
    unfold x
    rw [pow_two]
  have ht2Pow : m31Value t2 = x ^ 3 := by
    rw [ht2Value, hx2Pow]
    unfold x
    rw [show 3 = 2 + 1 by norm_num, pow_add, pow_one]
  have ht2Squared2Pow : m31Value t2Squared2 = x ^ 12 := by
    rw [ht2Squared2Value, ht2Pow, ← pow_mul]
    norm_num
  have ht4Pow : m31Value t4 = x ^ 15 := by
    rw [ht4Value, ht2Squared2Pow, ht2Pow, ← pow_add]
  have ht4Squared4Pow : m31Value t4Squared4 = x ^ 240 := by
    rw [ht4Squared4Value, ht4Pow, ← pow_mul]
    norm_num
  have ht8Pow : m31Value t8 = x ^ 255 := by
    rw [ht8Value, ht4Squared4Pow, ht4Pow, ← pow_add]
  have ht8Squared8Pow : m31Value t8Squared8 = x ^ 65280 := by
    rw [ht8Squared8Value, ht8Pow, ← pow_mul]
    norm_num
  have ht16Pow : m31Value t16 = x ^ 65535 := by
    rw [ht16Value, ht8Squared8Pow, ht8Pow, ← pow_add]
  have ht16Squared8Pow : m31Value t16Squared8 = x ^ 16776960 := by
    rw [ht16Squared8Value, ht16Pow, ← pow_mul]
    norm_num
  have ht24Pow : m31Value t24 = x ^ 16777215 := by
    rw [ht24Value, ht16Squared8Pow, ht8Pow, ← pow_add]
  have ht24Squared4Pow : m31Value t24Squared4 = x ^ 268435440 := by
    rw [ht24Squared4Value, ht24Pow, ← pow_mul]
    norm_num
  have ht28Pow : m31Value t28 = x ^ 268435455 := by
    rw [ht28Value, ht24Squared4Pow, ht4Pow, ← pow_add]
  have ht28SquaredPow : m31Value t28Squared = x ^ 536870910 := by
    rw [ht28SquaredValue, ht28Pow, ← pow_add]
  have ht29Pow : m31Value t29 = x ^ 536870911 := by
    rw [ht29Value, ht28SquaredPow]
    change x ^ 536870910 * x = _
    rw [← pow_succ]
  have ht30Pow : m31Value t30 = x ^ 1073741822 := by
    rw [ht30Value, ht29Pow, ← pow_add]
  have ht30SquaredPow : m31Value t30Squared = x ^ 2147483644 := by
    rw [ht30SquaredValue, ht30Pow, ← pow_add]
  have houtputPow : m31Value output = x ^ 2147483645 := by
    rw [houtputValue, ht30SquaredPow]
    change x ^ 2147483644 * x = _
    rw [← pow_succ]
  have hpowInv : x ^ (P - 2) = x⁻¹ := by
    by_cases hx : x = 0
    · rw [hx, zero_pow (show P - 2 ≠ 0 by norm_num [P]), inv_zero]
    · rw [inv_eq_one_div, eq_div_iff hx, ← pow_succ,
        show (P - 2) + 1 = P - 1 by norm_num [P]]
      exact ZMod.pow_card_sub_one_eq_one hx
  refine ⟨output, hrun, houtputCanonical, ?_⟩
  rw [houtputPow, show 2147483645 = P - 2 by norm_num [P], hpowInv]

#print axioms point_add_corresponds
#print axioms canonical_eq_of_m31Value_eq
#print axioms double_point_corresponds
#print axioms double_produces_canonical
#print axioms is_zero_false
#print axioms double_x_produces_canonical
#print axioms square_n_corresponds
#print axioms inv_output_canonical
#print axioms inv_produces_exact

end AspisV5FriCoordinateFieldSemantics
