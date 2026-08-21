import V5FriConsumerValueSemantics

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriTransparentHelperEquality

open AspisV5FriConsumerValueSemantics
open AspisV5FriArithmeticSemantics
open AspisV5FriPreparedSumSemantics

@[simp] theorem to_source_qm31_eq_to_arithmetic
    (value : V5FriConsumerExact.HelperTransport.Consumer.QM31) :
    V5FriConsumerExact.HelperTransport.toSourceQM31 value =
      V5FriConsumerExact.HelperTransport.toArithmeticQM31 value := rfl

@[simp] theorem from_source_qm31_eq_from_arithmetic
    (value : V5FriArithmeticExact.field.QM31) :
    V5FriConsumerExact.HelperTransport.fromSourceQM31 value =
      V5FriConsumerExact.HelperTransport.fromArithmeticQM31 value := rfl

@[simp] theorem to_source_prepared_eq_to_arithmetic
    (value : V5FriConsumerExact.HelperTransport.Consumer.Prepared) :
    V5FriConsumerExact.HelperTransport.toSourcePrepared value =
      V5FriConsumerExact.HelperTransport.toArithmeticPrepared value := rfl

@[simp] theorem map_to_source_qm31_eq_map_to_arithmetic
    {N : Std.Usize}
    (values : Array V5FriConsumerExact.HelperTransport.Consumer.QM31 N) :
    V5FriConsumerExact.HelperTransport.mapArray
        V5FriConsumerExact.HelperTransport.toSourceQM31 values =
      V5FriConsumerExact.HelperTransport.mapArray
        V5FriConsumerExact.HelperTransport.toArithmeticQM31 values := by
  rfl

@[simp] theorem map_to_source_prepared_eq_map_to_arithmetic
    {N : Std.Usize}
    (values : Array V5FriConsumerExact.HelperTransport.Consumer.Prepared N) :
    V5FriConsumerExact.HelperTransport.mapArray
        V5FriConsumerExact.HelperTransport.toSourcePrepared values =
      V5FriConsumerExact.HelperTransport.mapArray
        V5FriConsumerExact.HelperTransport.toArithmeticPrepared values := by
  rfl

@[simp] theorem map_result_from_source_qm31_eq_from_arithmetic
    (value : Result V5FriArithmeticExact.field.QM31) :
    V5FriConsumerExact.HelperTransport.mapResult
        V5FriConsumerExact.HelperTransport.fromSourceQM31 value =
      V5FriConsumerExact.HelperTransport.mapResult
        V5FriConsumerExact.HelperTransport.fromArithmeticQM31 value := by
  cases value <;> rfl

@[simp] theorem source_p_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.field.P =
      V5FriArithmeticExact.field.P := by
  simp [V5FriHelperTransparent.aspis_core.field.P,
    V5FriArithmeticExact.field.P]

@[simp] theorem source_reduce_u64_eq_arithmetic (value : Std.U64) :
    V5FriHelperTransparent.aspis_core.field.reduce_u64 value =
      V5FriArithmeticExact.field.reduce_u64 value := by
  simp [V5FriHelperTransparent.aspis_core.field.reduce_u64,
    V5FriArithmeticExact.field.reduce_u64,
    V5FriHelperTransparent.aspis_core.field.P,
    V5FriArithmeticExact.field.P]

@[simp] theorem source_m31_reduce_u64_eq_arithmetic (value : Std.U64) :
    V5FriHelperTransparent.aspis_core.field.M31.reduce_u64 value =
      V5FriArithmeticExact.field.M31.reduce_u64 value := by
  simp [V5FriHelperTransparent.aspis_core.field.M31.reduce_u64,
    V5FriArithmeticExact.field.M31.reduce_u64]

@[simp] theorem source_m31_add_eq_arithmetic
    (left right : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.field.M31.add left right =
      V5FriArithmeticExact.field.M31.add left right := by
  simp [V5FriHelperTransparent.aspis_core.field.M31.add,
    V5FriArithmeticExact.field.M31.add,
    V5FriHelperTransparent.aspis_core.field.P,
    V5FriArithmeticExact.field.P]

@[simp] theorem source_m31_sub_eq_arithmetic
    (left right : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.field.M31.sub left right =
      V5FriArithmeticExact.field.M31.sub left right := by
  simp [V5FriHelperTransparent.aspis_core.field.M31.sub,
    V5FriArithmeticExact.field.M31.sub,
    V5FriHelperTransparent.aspis_core.field.P,
    V5FriArithmeticExact.field.P]

@[simp] theorem source_cm31_add_eq_arithmetic
    (left right : V5FriArithmeticExact.field.CM31) :
    V5FriHelperTransparent.aspis_core.field.CM31.add left right =
      V5FriArithmeticExact.field.CM31.add left right := by
  simp [V5FriHelperTransparent.aspis_core.field.CM31.add,
    V5FriArithmeticExact.field.CM31.add]

@[simp] theorem source_cm31_sub_eq_arithmetic
    (left right : V5FriArithmeticExact.field.CM31) :
    V5FriHelperTransparent.aspis_core.field.CM31.sub left right =
      V5FriArithmeticExact.field.CM31.sub left right := by
  simp [V5FriHelperTransparent.aspis_core.field.CM31.sub,
    V5FriArithmeticExact.field.CM31.sub]

@[simp] theorem source_m31_double_eq_arithmetic
    (value : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.field.M31.double value =
      V5FriArithmeticExact.field.M31.double value := by
  simp [V5FriHelperTransparent.aspis_core.field.M31.double,
    V5FriArithmeticExact.field.M31.double]

@[simp] theorem source_mul_by_r_eq_arithmetic
    (value : V5FriArithmeticExact.field.CM31) :
    V5FriHelperTransparent.aspis_core.field.mul_by_r value =
      V5FriArithmeticExact.field.mul_by_r value := by
  simp [V5FriHelperTransparent.aspis_core.field.mul_by_r,
    V5FriArithmeticExact.field.mul_by_r]

@[simp] theorem source_m31_mul_eq_arithmetic
    (left right : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.field.M31.mul left right =
      V5FriArithmeticExact.field.M31.mul left right := by
  simp [V5FriHelperTransparent.aspis_core.field.M31.mul,
    V5FriArithmeticExact.field.M31.mul]

@[simp] theorem source_cm31_mul_m31_eq_arithmetic
    (left : V5FriArithmeticExact.field.CM31)
    (right : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.field.CM31.mul_m31 left right =
      V5FriArithmeticExact.field.CM31.mul_m31 left right := by
  simp [V5FriHelperTransparent.aspis_core.field.CM31.mul_m31,
    V5FriArithmeticExact.field.CM31.mul_m31]

@[simp] theorem source_qm31_mul_m31_eq_arithmetic
    (left : V5FriArithmeticExact.field.QM31)
    (right : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.field.QM31.mul_m31 left right =
      V5FriArithmeticExact.field.QM31.mul_m31 left right := by
  simp [V5FriHelperTransparent.aspis_core.field.QM31.mul_m31,
    V5FriArithmeticExact.field.QM31.mul_m31]

@[simp] theorem source_qm31_add_eq_arithmetic
    (left right : V5FriArithmeticExact.field.QM31) :
    V5FriHelperTransparent.aspis_core.field.QM31.add left right =
      V5FriArithmeticExact.field.QM31.add left right := by
  simp [V5FriHelperTransparent.aspis_core.field.QM31.add,
    V5FriArithmeticExact.field.QM31.add]

@[simp] theorem source_qm31_sub_eq_arithmetic
    (left right : V5FriArithmeticExact.field.QM31) :
    V5FriHelperTransparent.aspis_core.field.QM31.sub left right =
      V5FriArithmeticExact.field.QM31.sub left right := by
  simp [V5FriHelperTransparent.aspis_core.field.QM31.sub,
    V5FriArithmeticExact.field.QM31.sub]

@[simp] theorem source_m31_half_eq_arithmetic
    (value : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.field.M31.half value =
      V5FriArithmeticExact.field.M31.half value := by
  simp [V5FriHelperTransparent.aspis_core.field.M31.half,
    V5FriArithmeticExact.field.M31.half,
    V5FriHelperTransparent.aspis_core.field.P,
    V5FriArithmeticExact.field.P,
    Std.U32.wrapping_shr,
    Std.U64.wrapping_shr,
    UScalar.wrapping_shr,
    ScalarShiftAmount.toNat]

@[simp] theorem source_cm31_half_eq_arithmetic
    (value : V5FriArithmeticExact.field.CM31) :
    V5FriHelperTransparent.aspis_core.field.CM31.half value =
      V5FriArithmeticExact.field.CM31.half value := by
  simp [V5FriHelperTransparent.aspis_core.field.CM31.half,
    V5FriArithmeticExact.field.CM31.half]

@[simp] theorem source_qm31_half_eq_arithmetic
    (value : V5FriArithmeticExact.field.QM31) :
    V5FriHelperTransparent.aspis_core.field.QM31.half value =
      V5FriArithmeticExact.field.QM31.half value := by
  simp [V5FriHelperTransparent.aspis_core.field.QM31.half,
    V5FriArithmeticExact.field.QM31.half]

theorem source_cm31_mul_corresponds
    (left right : V5FriArithmeticExact.field.CM31)
    (hleft : canonicalCM31 left) (hright : canonicalCM31 right) :
    ∃ output,
      V5FriHelperTransparent.aspis_core.field.CM31.mul left right =
        .ok output ∧
      canonicalCM31 output ∧
      cm31View output = cm31View left * cm31View right := by
  rcases m31_mul_corresponds left.a right.a hleft.1 hright.1 with
    ⟨m0, hm0, hm0Canonical, hm0Exact⟩
  rcases m31_mul_corresponds left.b right.b hleft.2 hright.2 with
    ⟨m1, hm1, hm1Canonical, hm1Exact⟩
  rcases m31_add_corresponds left.a left.b hleft.1 hleft.2 with
    ⟨leftSum, hleftSum, hleftSumCanonical, hleftSumExact⟩
  rcases m31_add_corresponds right.a right.b hright.1 hright.2 with
    ⟨rightSum, hrightSum, hrightSumCanonical, hrightSumExact⟩
  rcases m31_mul_corresponds leftSum rightSum hleftSumCanonical
      hrightSumCanonical with
    ⟨m2, hm2, hm2Canonical, hm2Exact⟩
  rcases m31_sub_corresponds m0 m1 hm0Canonical hm1Canonical with
    ⟨real, hreal, hrealCanonical, hrealExact⟩
  rcases m31_sub_corresponds m2 m0 hm2Canonical hm0Canonical with
    ⟨imagPartial, himagPartial, himagPartialCanonical, himagPartialExact⟩
  rcases m31_sub_corresponds imagPartial m1 himagPartialCanonical
      hm1Canonical with
    ⟨imag, himag, himagCanonical, himagExact⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [V5FriHelperTransparent.aspis_core.field.CM31.mul,
      hm0, hm1, hleftSum, hrightSum, hm2, hreal, himagPartial, himag]
  · apply QuadraticAlgebra.ext
    · simp only [cm31View, QuadraticAlgebra.re_mul]
      rw [hrealExact, hm0Exact, hm1Exact]
      ring
    · simp only [cm31View, QuadraticAlgebra.im_mul]
      rw [himagExact, himagPartialExact, hm2Exact, hm0Exact, hm1Exact,
        hleftSumExact, hrightSumExact]
      ring

theorem source_cm31_square_corresponds
    (value : V5FriArithmeticExact.field.CM31)
    (hvalue : canonicalCM31 value) :
    ∃ output,
      V5FriHelperTransparent.aspis_core.field.CM31.square value =
        .ok output ∧
      canonicalCM31 output ∧
      cm31View output = cm31View value * cm31View value := by
  rcases m31_add_corresponds value.a value.b hvalue.1 hvalue.2 with
    ⟨sum, hsum, hsumCanonical, hsumExact⟩
  rcases m31_sub_corresponds value.a value.b hvalue.1 hvalue.2 with
    ⟨difference, hdifference, hdifferenceCanonical, hdifferenceExact⟩
  rcases m31_mul_corresponds sum difference hsumCanonical
      hdifferenceCanonical with
    ⟨real, hreal, hrealCanonical, hrealExact⟩
  rcases m31_mul_corresponds value.a value.b hvalue.1 hvalue.2 with
    ⟨product, hproduct, hproductCanonical, hproductExact⟩
  rcases m31_double_corresponds product hproductCanonical with
    ⟨imag, himag, himagCanonical, himagExact⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [V5FriHelperTransparent.aspis_core.field.CM31.square,
      hsum, hdifference, hreal, hproduct, himag]
  · apply QuadraticAlgebra.ext
    · simp only [cm31View, QuadraticAlgebra.re_mul]
      rw [hrealExact, hsumExact, hdifferenceExact]
      ring
    · simp only [cm31View, QuadraticAlgebra.im_mul]
      rw [himagExact, hproductExact]
      ring

theorem source_cm31_double_corresponds
    (value : V5FriArithmeticExact.field.CM31)
    (hvalue : canonicalCM31 value) :
    ∃ output,
      V5FriHelperTransparent.aspis_core.field.CM31.double value =
        .ok output ∧
      canonicalCM31 output ∧
      cm31View output = cm31View value + cm31View value := by
  rcases cm31_add_corresponds value value hvalue hvalue with
    ⟨output, hcall, hcanonical, hexact⟩
  exact ⟨output, by
    simpa [V5FriHelperTransparent.aspis_core.field.CM31.double] using hcall,
    hcanonical, hexact⟩

theorem source_qm31_mul_corresponds
    (left right : V5FriArithmeticExact.field.QM31)
    (hleft : canonicalQM31 left) (hright : canonicalQM31 right) :
    ∃ output,
      V5FriHelperTransparent.aspis_core.field.QM31.mul left right =
        .ok output ∧
      canonicalQM31 output ∧
      qm31View output = qm31View left * qm31View right := by
  rcases source_cm31_mul_corresponds left.c0 right.c0 hleft.1 hright.1 with
    ⟨m0, hm0, hm0Canonical, hm0Exact⟩
  rcases source_cm31_mul_corresponds left.c1 right.c1 hleft.2 hright.2 with
    ⟨m1, hm1, hm1Canonical, hm1Exact⟩
  rcases cm31_add_corresponds left.c0 left.c1 hleft.1 hleft.2 with
    ⟨leftSum, hleftSum, hleftSumCanonical, hleftSumExact⟩
  rcases cm31_add_corresponds right.c0 right.c1 hright.1 hright.2 with
    ⟨rightSum, hrightSum, hrightSumCanonical, hrightSumExact⟩
  rcases source_cm31_mul_corresponds leftSum rightSum hleftSumCanonical
      hrightSumCanonical with
    ⟨m2, hm2, hm2Canonical, hm2Exact⟩
  rcases mul_by_r_corresponds m1 hm1Canonical with
    ⟨rTimesM1, hrTimesM1, hrTimesM1Canonical, hrTimesM1Exact⟩
  rcases cm31_add_corresponds m0 rTimesM1 hm0Canonical
      hrTimesM1Canonical with
    ⟨low, hlow, hlowCanonical, hlowExact⟩
  rcases cm31_sub_corresponds m2 m0 hm2Canonical hm0Canonical with
    ⟨highPartial, hhighPartial, hhighPartialCanonical, hhighPartialExact⟩
  rcases cm31_sub_corresponds highPartial m1 hhighPartialCanonical
      hm1Canonical with
    ⟨high, hhigh, hhighCanonical, hhighExact⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hlowCanonical, hhighCanonical⟩, ?_⟩
  · simp [V5FriHelperTransparent.aspis_core.field.QM31.mul,
      hm0, hm1, hleftSum, hrightSum, hm2, hrTimesM1, hlow,
      hhighPartial, hhigh]
  · apply QuadraticAlgebra.ext
    · simp only [qm31View, QuadraticAlgebra.re_mul]
      rw [hlowExact, hm0Exact, hrTimesM1Exact, hm1Exact]
      ring
    · simp only [qm31View, QuadraticAlgebra.im_mul]
      rw [hhighExact, hhighPartialExact, hm2Exact, hm0Exact, hm1Exact,
        hleftSumExact, hrightSumExact]
      ring

theorem source_qm31_square_corresponds
    (value : V5FriArithmeticExact.field.QM31)
    (hvalue : canonicalQM31 value) :
    ∃ output,
      V5FriHelperTransparent.aspis_core.field.QM31.square value =
        .ok output ∧
      canonicalQM31 output ∧
      qm31View output = qm31View value * qm31View value := by
  rcases source_cm31_square_corresponds value.c0 hvalue.1 with
    ⟨c0Square, hc0Square, hc0SquareCanonical, hc0SquareExact⟩
  rcases source_cm31_square_corresponds value.c1 hvalue.2 with
    ⟨c1Square, hc1Square, hc1SquareCanonical, hc1SquareExact⟩
  rcases mul_by_r_corresponds c1Square hc1SquareCanonical with
    ⟨rTimesC1Square, hrTimes, hrTimesCanonical, hrTimesExact⟩
  rcases cm31_add_corresponds c0Square rTimesC1Square hc0SquareCanonical
      hrTimesCanonical with
    ⟨low, hlow, hlowCanonical, hlowExact⟩
  rcases source_cm31_mul_corresponds value.c0 value.c1 hvalue.1 hvalue.2 with
    ⟨cross, hcross, hcrossCanonical, hcrossExact⟩
  rcases source_cm31_double_corresponds cross hcrossCanonical with
    ⟨high, hhigh, hhighCanonical, hhighExact⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hlowCanonical, hhighCanonical⟩, ?_⟩
  · simp [V5FriHelperTransparent.aspis_core.field.QM31.square,
      hc0Square, hc1Square, hrTimes, hlow, hcross, hhigh]
  · apply QuadraticAlgebra.ext
    · simp only [qm31View, QuadraticAlgebra.re_mul]
      rw [hlowExact, hc0SquareExact, hrTimesExact, hc1SquareExact]
      ring
    · simp only [qm31View, QuadraticAlgebra.im_mul]
      rw [hhighExact, hcrossExact]
      ring

theorem source_prepared_new_represents
    (value : V5FriArithmeticExact.field.QM31)
    (hvalue : canonicalQM31 value) :
    ∃ output,
      V5FriHelperTransparent.aspis_core.field.PreparedQm31Multiplier.new
          value = .ok output ∧
      PreparedRepresents output (qm31View value) := by
  rcases m31_add_corresponds value.c0.a value.c0.b hvalue.1.1 hvalue.1.2 with
    ⟨sum0, hsum0, hsum0Canonical, hsum0Exact⟩
  rcases m31_add_corresponds value.c1.a value.c1.b hvalue.2.1 hvalue.2.2 with
    ⟨sum1, hsum1, hsum1Canonical, hsum1Exact⟩
  rcases cm31_add_corresponds value.c0 value.c1 hvalue.1 hvalue.2 with
    ⟨component2, hcomponent2, hcomponent2Canonical, hcomponent2Exact⟩
  rcases m31_add_corresponds component2.a component2.b
      hcomponent2Canonical.1 hcomponent2Canonical.2 with
    ⟨sum2, hsum2, hsum2Canonical, hsum2Exact⟩
  let row0 : Array V5FriArithmeticExact.field.M31 3#usize :=
    Array.make 3#usize [value.c0.a, value.c0.b, sum0]
  let row1 : Array V5FriArithmeticExact.field.M31 3#usize :=
    Array.make 3#usize [value.c1.a, value.c1.b, sum1]
  let row2 : Array V5FriArithmeticExact.field.M31 3#usize :=
    Array.make 3#usize [component2.a, component2.b, sum2]
  let output : V5FriArithmeticExact.field.PreparedQm31Multiplier :=
    ⟨Array.make 3#usize [row0, row1, row2]⟩
  refine ⟨output, ?_, ?_⟩
  · simp [V5FriHelperTransparent.aspis_core.field.PreparedQm31Multiplier.new,
      V5FriHelperTransparent.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
      hsum0, hsum1, hcomponent2, hsum2, row0, row1, row2, output]
  · intro component hComponent channel hChannel
    have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
    have hh : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
    rcases hc with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
    all_goals
      simp [
        AspisLane5QM31SumProductsProof.channelM31,
        output, row0, row1, row2, Aeneas.Std.Array.make,
        exactInputChannel, exactQMComponent, exactCMChannel,
        qm31View, cm31View]
    · exact hvalue.1.1
    · exact hvalue.1.2
    · exact ⟨hsum0Canonical, hsum0Exact⟩
    · exact hvalue.2.1
    · exact hvalue.2.2
    · exact ⟨hsum1Canonical, hsum1Exact⟩
    · refine ⟨hcomponent2Canonical.1, ?_⟩
      have hreal := congrArg QuadraticAlgebra.re hcomponent2Exact
      simpa only [cm31View, QuadraticAlgebra.re_add] using hreal
    · refine ⟨hcomponent2Canonical.2, ?_⟩
      have himag := congrArg QuadraticAlgebra.im hcomponent2Exact
      simpa only [cm31View, QuadraticAlgebra.im_add] using himag
    · refine ⟨hsum2Canonical, ?_⟩
      have hreal := congrArg QuadraticAlgebra.re hcomponent2Exact
      have himag := congrArg QuadraticAlgebra.im hcomponent2Exact
      simp only [cm31View, QuadraticAlgebra.re_add] at hreal
      simp only [cm31View, QuadraticAlgebra.im_add] at himag
      rw [hsum2Exact, hreal, himag]

@[simp] theorem source_sum_eq_arithmetic
    (left : Array V5FriArithmeticExact.field.PreparedQm31Multiplier 3#usize)
    (right : Array V5FriArithmeticExact.field.QM31 3#usize) :
    V5FriHelperTransparent.aspis_core.field.qm31_sum_products3_prepared left right =
      V5FriArithmeticExact.field.qm31_sum_products3_prepared left right := by
  simp [V5FriHelperTransparent.aspis_core.field.qm31_sum_products3_prepared,
    V5FriArithmeticExact.field.qm31_sum_products3_prepared,
    V5FriHelperTransparent.aspis_core.field.qm31_sum_products3_prepared_loop0,
    V5FriArithmeticExact.field.qm31_sum_products3_prepared_loop0,
    V5FriHelperTransparent.aspis_core.field.qm31_sum_products3_prepared_loop0.body,
    V5FriArithmeticExact.field.qm31_sum_products3_prepared_loop0.body,
    V5FriHelperTransparent.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0,
    V5FriArithmeticExact.field.qm31_sum_products3_prepared_loop0_loop0,
    V5FriHelperTransparent.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0.body,
    V5FriArithmeticExact.field.qm31_sum_products3_prepared_loop0_loop0.body,
    V5FriHelperTransparent.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0,
    V5FriArithmeticExact.field.qm31_sum_products3_prepared_loop0_loop0_loop0,
    V5FriHelperTransparent.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0.body,
    V5FriArithmeticExact.field.qm31_sum_products3_prepared_loop0_loop0_loop0.body,
    V5FriHelperTransparent.aspis_core.field.qm31_from_karatsuba_channel_sums,
    V5FriArithmeticExact.field.qm31_from_karatsuba_channel_sums,
    V5FriHelperTransparent.aspis_core.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    V5FriArithmeticExact.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call] <;>
    rfl

theorem circle_transport_call
    (values : Array V5FriConsumerExact.HelperTransport.Consumer.QM31 4#usize)
    (alphaPowers : Array V5FriConsumerExact.HelperTransport.Consumer.Prepared 3#usize)
    (inv2x inv2y : V5FriConsumerExact.HelperTransport.Consumer.M31) :
    V5FriConsumerExact.HelperTransport.circle values alphaPowers inv2x inv2y =
      V5FriConsumerExact.HelperTransport.mapResult
        V5FriConsumerExact.HelperTransport.fromArithmeticQM31
        (V5FriArithmeticExact.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
          (V5FriConsumerExact.HelperTransport.mapArray
            V5FriConsumerExact.HelperTransport.toArithmeticQM31 values)
          (V5FriConsumerExact.HelperTransport.mapArray
            V5FriConsumerExact.HelperTransport.toArithmeticPrepared alphaPowers)
          inv2x inv2y) := by
  simp [V5FriConsumerExact.HelperTransport.circle,
    V5FriHelperTransparent.circle,
    V5FriHelperTransparent.aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs,
    V5FriArithmeticExact.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs,
    V5FriHelperTransparent.aspis_core.field.M31.neg,
    V5FriArithmeticExact.field.M31.neg,
    V5FriHelperTransparent.aspis_core.field.P,
    V5FriArithmeticExact.field.P,
    V5FriHelperTransparent.aspis_core.circle_fri.normalized_arity4_prepared_polynomial_candidate,
    V5FriArithmeticExact.circle_fri.normalized_arity4_prepared_polynomial_candidate]

@[simp] theorem source_decode_later_call_mut_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut =
      V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut := by
  funext closure value
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut,
    V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut,
    V5FriHelperTransparent.aspis_core.field.P,
    V5FriArithmeticExact.field.P]

@[simp] theorem source_decode_later_call_once_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once =
      V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once := by
  funext closure value
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once,
    V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once]

@[simp] theorem source_decode_later_fnmut_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool =
      V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool := by
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool,
    V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool,
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool,
    V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool]

@[simp] theorem source_iter_mut_enumerate_next_eq_arithmetic {T : Type} :
    @V5FriHelperTransparent.iterMutEnumerateNext T =
      @V5FriArithmeticExact.iterMutEnumerateNext T := by
  rfl

@[simp] theorem source_circle_query_qm31_bytes_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES =
      V5FriArithmeticExact.circle_query.CIRCLE_QUERY_QM31_BYTES := by
  simp [V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES,
    V5FriArithmeticExact.circle_query.CIRCLE_QUERY_QM31_BYTES]

@[simp] theorem source_cm31_new_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.field.CM31.new =
      V5FriArithmeticExact.field.CM31.new := by
  funext a b
  rfl

@[simp] theorem source_later_leaf_eq_arithmetic (layer : Std.U8) :
    V5FriHelperTransparent.aspis_core.circle_query.CircleQueryLeaf.Later layer =
      V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer := by
  rfl

@[simp] theorem source_noncanonical_qm31_eq_arithmetic
    (layer : Std.U8) (offset : Std.Usize) :
    V5FriHelperTransparent.aspis_core.circle_query.CircleQueryError.NonCanonicalQm31
        (V5FriHelperTransparent.aspis_core.circle_query.CircleQueryLeaf.Later layer)
        offset =
      V5FriArithmeticExact.circle_query.CircleQueryError.NonCanonicalQm31
        (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer)
        offset := by
  rfl

@[simp] theorem source_leaf_length_eq_arithmetic
    (layer : Std.U8) (expected actual : Std.Usize) :
    V5FriHelperTransparent.aspis_core.circle_query.CircleQueryError.LeafLength
        (V5FriHelperTransparent.aspis_core.circle_query.CircleQueryLeaf.Later layer)
        expected actual =
      V5FriArithmeticExact.circle_query.CircleQueryError.LeafLength
        (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer)
        expected actual := by
  rfl

@[simp] theorem source_query_out_of_range_eq_arithmetic (query : Std.Usize) :
    V5FriHelperTransparent.aspis_core.circle_query.CircleQueryError.QueryOutOfRange query =
      V5FriArithmeticExact.circle_query.CircleQueryError.QueryOutOfRange query := by
  rfl

@[simp] theorem source_decode_later_body_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop.body =
      V5FriArithmeticExact.circle_query.decode_later_leaf_loop.body := by
  funext toSliceBack iterBack enumerateBack leaf layer iter back
  unfold
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop.body
    V5FriArithmeticExact.circle_query.decode_later_leaf_loop.body
  rw [source_iter_mut_enumerate_next_eq_arithmetic,
    source_decode_later_fnmut_eq_arithmetic,
    source_circle_query_qm31_bytes_eq_arithmetic,
    source_cm31_new_eq_arithmetic]
  simp [source_noncanonical_qm31_eq_arithmetic]
  intro item nextState nextBack hNext
  cases item <;> rfl

@[simp] theorem source_decode_later_loop_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop =
      V5FriArithmeticExact.circle_query.decode_later_leaf_loop := by
  funext toSliceBack iterBack enumerateBack iter back leaf layer
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop,
    V5FriArithmeticExact.circle_query.decode_later_leaf_loop]

theorem source_decode_later_leaf_eq_arithmetic
    (leaf : Slice Std.U8) (layer : Std.U8) :
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf
        leaf layer =
      V5FriArithmeticExact.circle_query.decode_later_leaf leaf layer := by
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf,
    V5FriArithmeticExact.circle_query.decode_later_leaf,
    V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES,
    V5FriArithmeticExact.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES,
    V5FriHelperTransparent.aspis_core.circle_query.check_leaf_length,
    V5FriArithmeticExact.circle_query.check_leaf_length,
    V5FriHelperTransparent.aspis_core.field.QM31.ZERO,
    V5FriArithmeticExact.field.QM31.ZERO,
    V5FriHelperTransparent.iterMutEnumerate,
    V5FriArithmeticExact.iterMutEnumerate,
    source_decode_later_loop_eq_arithmetic]
  intro expected hExpected checked hChecked flow hFlow
  cases flow <;> rfl

@[simp] theorem source_decode_selected_call_mut_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut =
      V5FriArithmeticExact.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut := by
  funext closure value
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut,
    V5FriArithmeticExact.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut,
    V5FriHelperTransparent.aspis_core.field.P,
    V5FriArithmeticExact.field.P]

@[simp] theorem source_decode_selected_call_once_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once =
      V5FriArithmeticExact.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once := by
  funext closure value
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once,
    V5FriArithmeticExact.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once]

@[simp] theorem source_decode_selected_fnmut_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool =
      V5FriArithmeticExact.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool := by
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool,
    V5FriArithmeticExact.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool,
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool,
    V5FriArithmeticExact.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool]

@[simp] theorem source_decode_selected_body_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot_loop.body =
      V5FriArithmeticExact.circle_query.decode_selected_later_slot_loop.body := by
  funext leaf layer selectedSlot iter selected
  unfold
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot_loop.body
    V5FriArithmeticExact.circle_query.decode_selected_later_slot_loop.body
  rw [source_decode_selected_fnmut_eq_arithmetic]
  simp [V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES,
    V5FriArithmeticExact.circle_query.CIRCLE_QUERY_QM31_BYTES,
    V5FriHelperTransparent.aspis_core.field.CM31.new,
    V5FriArithmeticExact.field.CM31.new,
    source_noncanonical_qm31_eq_arithmetic]
  intro item nextState hNext
  cases item <;> rfl

@[simp] theorem source_decode_selected_loop_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot_loop =
      V5FriArithmeticExact.circle_query.decode_selected_later_slot_loop := by
  funext iter leaf layer selectedSlot selected
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot_loop,
    V5FriArithmeticExact.circle_query.decode_selected_later_slot_loop]

theorem source_decode_selected_later_slot_eq_arithmetic
    (leaf : Slice Std.U8) (layer : Std.U8) (selectedSlot : Std.Usize) :
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot
        leaf layer selectedSlot =
      V5FriArithmeticExact.circle_query.decode_selected_later_slot
        leaf layer selectedSlot := by
  simp [V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot,
    V5FriArithmeticExact.circle_query.decode_selected_later_slot,
    V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES,
    V5FriArithmeticExact.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES,
    V5FriHelperTransparent.aspis_core.circle_query.check_leaf_length,
    V5FriArithmeticExact.circle_query.check_leaf_length,
    source_decode_selected_loop_eq_arithmetic]
  intro expected hExpected checked hChecked flow hFlow
  cases flow <;> rfl

@[simp] theorem source_normalized_line_eq_arithmetic
    (values : Array V5FriArithmeticExact.field.QM31 4#usize)
    (alphaPowers : Array V5FriArithmeticExact.field.PreparedQm31Multiplier 3#usize)
    (inverses : Array V5FriArithmeticExact.field.M31 3#usize) :
    V5FriHelperTransparent.aspis_core.circle_fri.normalized_line_arity4_prepared_polynomial_refs
        values alphaPowers inverses =
      V5FriArithmeticExact.circle_fri.normalized_line_arity4_prepared_polynomial_refs
        values alphaPowers inverses := by
  simp [V5FriHelperTransparent.aspis_core.circle_fri.normalized_line_arity4_prepared_polynomial_refs,
    V5FriArithmeticExact.circle_fri.normalized_line_arity4_prepared_polynomial_refs,
    V5FriHelperTransparent.aspis_core.circle_fri.normalized_arity4_prepared_polynomial_candidate,
    V5FriArithmeticExact.circle_fri.normalized_arity4_prepared_polynomial_candidate]

@[simp] theorem source_m31_eq_eq_arithmetic
    (left right : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
        left right =
      V5FriArithmeticExact.field.M31.Insts.CoreCmpPartialEqM31.eq left right := by
  simp [V5FriHelperTransparent.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    V5FriArithmeticExact.field.M31.Insts.CoreCmpPartialEqM31.eq]

@[simp] theorem source_cm31_eq_eq_arithmetic
    (left right : V5FriArithmeticExact.field.CM31) :
    V5FriHelperTransparent.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq
        left right =
      V5FriArithmeticExact.field.CM31.Insts.CoreCmpPartialEqCM31.eq left right := by
  simp [V5FriHelperTransparent.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    V5FriArithmeticExact.field.CM31.Insts.CoreCmpPartialEqCM31.eq]

@[simp] theorem source_qm31_eq_eq_arithmetic
    (left right : V5FriArithmeticExact.field.QM31) :
    V5FriHelperTransparent.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
        left right =
      V5FriArithmeticExact.field.QM31.Insts.CoreCmpPartialEqQM31.eq left right := by
  simp [V5FriHelperTransparent.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    V5FriArithmeticExact.field.QM31.Insts.CoreCmpPartialEqQM31.eq]

@[simp] theorem source_qm31_partial_eq_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 =
      V5FriArithmeticExact.field.QM31.Insts.CoreCmpPartialEqQM31 := by
  simp [V5FriHelperTransparent.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,
    V5FriArithmeticExact.field.QM31.Insts.CoreCmpPartialEqQM31]
  constructor
  · funext left right
    exact source_qm31_eq_eq_arithmetic left right
  · funext left right
    simp [core.cmp.PartialEq.ne.default,
      source_qm31_eq_eq_arithmetic]

@[simp] theorem source_layer_mismatch_eq_arithmetic
    (layer : Std.U8) (offset : Std.Usize) :
    V5FriHelperTransparent.aspis_core.circle_query.CircleQueryError.LayerValueMismatch
        layer offset =
      V5FriArithmeticExact.circle_query.CircleQueryError.LayerValueMismatch
        layer offset := by
  rfl

@[simp] theorem source_terminal_mismatch_eq_arithmetic (index : Std.Usize) :
    V5FriHelperTransparent.aspis_core.circle_query.CircleQueryError.TerminalValueMismatch
        index =
      V5FriArithmeticExact.circle_query.CircleQueryError.TerminalValueMismatch
        index := by
  rfl

theorem source_line_call_eq_arithmetic
    (incoming outgoing : Slice Std.U8) (index : Std.Usize)
    (layer : Std.U8)
    (inverses : Array V5FriArithmeticExact.field.M31 3#usize)
    (alphaPowers : Array V5FriArithmeticExact.field.PreparedQm31Multiplier 3#usize) :
    V5FriHelperTransparent.aspis_core.circle_query.check_fixed_line_transition_prepared_polynomial_powers
        incoming outgoing index layer inverses alphaPowers =
      V5FriArithmeticExact.circle_query.check_fixed_line_transition_prepared_polynomial_powers
        incoming outgoing index layer inverses alphaPowers := by
  simp [V5FriHelperTransparent.aspis_core.circle_query.check_fixed_line_transition_prepared_polynomial_powers,
    V5FriArithmeticExact.circle_query.check_fixed_line_transition_prepared_polynomial_powers,
    source_decode_later_leaf_eq_arithmetic,
    source_decode_selected_later_slot_eq_arithmetic,
    source_normalized_line_eq_arithmetic,
    source_qm31_partial_eq_eq_arithmetic,
    V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES,
    V5FriArithmeticExact.circle_query.CIRCLE_QUERY_QM31_BYTES,
    source_layer_mismatch_eq_arithmetic]
  intro decoded hDecoded flow hFlow
  cases flow <;> rfl

@[simp] theorem source_m31_one_eq_arithmetic :
    V5FriHelperTransparent.aspis_core.field.M31.ONE =
      V5FriArithmeticExact.field.M31.ONE := by
  simp [V5FriHelperTransparent.aspis_core.field.M31.ONE,
    V5FriArithmeticExact.field.M31.ONE]

@[simp] theorem source_double_x_eq_arithmetic
    (x : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.circle_fri.double_x x =
      V5FriArithmeticExact.circle_fri.double_x x := by
  simp [V5FriHelperTransparent.aspis_core.circle_fri.double_x,
    V5FriArithmeticExact.circle_fri.double_x]

@[simp] theorem source_final_tensor_closure_call_eq_arithmetic
    (closure : Std.U32 × Std.U32 × Std.U32)
    (arguments : Std.U32 × Std.U32 × Std.U32) :
    V5FriHelperTransparent.aspis_core.circle_fri.evaluate_final_line_tensor_ref.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
        closure arguments =
      V5FriArithmeticExact.circle_fri.evaluate_final_line_tensor_ref.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call
        closure arguments := by
  simp [V5FriHelperTransparent.aspis_core.circle_fri.evaluate_final_line_tensor_ref.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call,
    V5FriArithmeticExact.circle_fri.evaluate_final_line_tensor_ref.closure.Insts.CoreOpsFunctionFnTupleM31M31M31M31.call]

@[simp] theorem source_final_tensor_eq_arithmetic
    (coefficients : Array V5FriArithmeticExact.field.QM31 4#usize)
    (x : V5FriArithmeticExact.field.M31) :
    V5FriHelperTransparent.aspis_core.circle_fri.evaluate_final_line_tensor_ref
        coefficients x =
      V5FriArithmeticExact.circle_fri.evaluate_final_line_tensor_ref
        coefficients x := by
  simp [V5FriHelperTransparent.aspis_core.circle_fri.evaluate_final_line_tensor_ref,
    V5FriArithmeticExact.circle_fri.evaluate_final_line_tensor_ref,
    source_double_x_eq_arithmetic,
    source_final_tensor_closure_call_eq_arithmetic,
    source_cm31_new_eq_arithmetic]

theorem source_terminal_call_eq_arithmetic
    (incoming : Slice Std.U8)
    (finalPolynomial : Array V5FriArithmeticExact.field.QM31 4#usize)
    (index : Std.Usize)
    (inverses : Array V5FriArithmeticExact.field.M31 3#usize)
    (finalX : V5FriArithmeticExact.field.M31)
    (alphaPowers : Array V5FriArithmeticExact.field.PreparedQm31Multiplier 3#usize) :
    V5FriHelperTransparent.aspis_core.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
        incoming finalPolynomial index inverses finalX alphaPowers =
      V5FriArithmeticExact.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
        incoming finalPolynomial index inverses finalX alphaPowers := by
  simp [V5FriHelperTransparent.aspis_core.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs,
    V5FriArithmeticExact.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs,
    source_decode_later_leaf_eq_arithmetic,
    source_normalized_line_eq_arithmetic,
    source_final_tensor_eq_arithmetic,
    source_qm31_partial_eq_eq_arithmetic,
    source_terminal_mismatch_eq_arithmetic]
  intro decoded hDecoded flow hFlow
  cases flow <;> rfl

@[simp] theorem helper_to_arithmetic_qm31_eq_to_exact
    (value : V5FriConsumerExact.HelperTransport.Consumer.QM31) :
    V5FriConsumerExact.HelperTransport.toArithmeticQM31 value =
      AspisV5FriConsumerValueSemantics.toExactQM31 value := by
  rfl

@[simp] theorem exact_of_source_roundtrip
    (value : V5FriArithmeticExact.field.QM31) :
    AspisV5FriConsumerValueSemantics.toExactQM31
        (V5FriConsumerExact.HelperTransport.fromSourceQM31 value) = value := by
  rfl

@[simp] theorem exact_of_arithmetic_roundtrip
    (value : V5FriArithmeticExact.field.QM31) :
    AspisV5FriConsumerValueSemantics.toExactQM31
        (V5FriConsumerExact.HelperTransport.fromArithmeticQM31 value) = value := by
  rfl

@[simp] theorem helper_map_qm31_eq_exact_map
    {N : Std.Usize}
    (values : Array V5FriConsumerExact.HelperTransport.Consumer.QM31 N) :
    V5FriConsumerExact.HelperTransport.mapArray
        V5FriConsumerExact.HelperTransport.toArithmeticQM31 values =
      AspisV5FriConsumerValueSemantics.mapArray
        AspisV5FriConsumerValueSemantics.toExactQM31 values := by
  rfl

@[simp] theorem helper_map_prepared_eq_exact_map
    {N : Std.Usize}
    (values : Array V5FriConsumerExact.HelperTransport.Consumer.Prepared N) :
    V5FriConsumerExact.HelperTransport.mapArray
        V5FriConsumerExact.HelperTransport.toArithmeticPrepared values =
      AspisV5FriConsumerValueSemantics.mapArray
        V5FriConsumerExact.HelperTransport.toArithmeticPrepared values := by
  rfl

@[simp] theorem arithmetic_prepared_of_source_roundtrip
    (value : V5FriArithmeticExact.field.PreparedQm31Multiplier) :
    V5FriConsumerExact.HelperTransport.toArithmeticPrepared
        (V5FriConsumerExact.HelperTransport.fromSourcePrepared value) = value := by
  rfl

theorem source_square_success
    (input output : V5FriArithmeticExact.field.QM31)
    (hCanonical : canonicalQM31 input)
    (hCall :
      V5FriHelperTransparent.aspis_core.field.QM31.square input = .ok output) :
    canonicalQM31 output ∧ qm31View output = qm31View input ^ 2 := by
  rcases source_qm31_square_corresponds input hCanonical with
    ⟨expected, hExpected, hExpectedCanonical, hExpectedValue⟩
  rw [hExpected] at hCall
  cases hCall
  exact ⟨hExpectedCanonical, by simpa [pow_two] using hExpectedValue⟩

theorem source_mul_success
    (left right output : V5FriArithmeticExact.field.QM31)
    (hLeft : canonicalQM31 left) (hRight : canonicalQM31 right)
    (hCall :
      V5FriHelperTransparent.aspis_core.field.QM31.mul left right = .ok output) :
    canonicalQM31 output ∧
      qm31View output = qm31View left * qm31View right := by
  rcases source_qm31_mul_corresponds left right hLeft hRight with
    ⟨expected, hExpected, hExpectedCanonical, hExpectedValue⟩
  rw [hExpected] at hCall
  cases hCall
  exact ⟨hExpectedCanonical, hExpectedValue⟩

theorem source_prepared_success
    (input : V5FriArithmeticExact.field.QM31)
    (output : V5FriArithmeticExact.field.PreparedQm31Multiplier)
    (hCanonical : canonicalQM31 input)
    (hCall :
      V5FriHelperTransparent.aspis_core.field.PreparedQm31Multiplier.new input =
        .ok output) :
    PreparedRepresents output (qm31View input) := by
  rcases source_prepared_new_represents input hCanonical with
    ⟨expected, hExpected, hRepresents⟩
  rw [hExpected] at hCall
  cases hCall
  exact hRepresents

theorem consumer_square_semantics
    (input output : AspisV5FriConsumerValueSemantics.Consumer.QM31)
    (hCanonical :
      canonicalQM31 (AspisV5FriConsumerValueSemantics.toExactQM31 input))
    (hCall :
      V5FriConsumerExact.aspis_core.field.QM31.square input = .ok output) :
    canonicalQM31 (AspisV5FriConsumerValueSemantics.toExactQM31 output) ∧
      qm31View (AspisV5FriConsumerValueSemantics.toExactQM31 output) =
        qm31View (AspisV5FriConsumerValueSemantics.toExactQM31 input) ^ 2 := by
  unfold V5FriConsumerExact.aspis_core.field.QM31.square
    V5FriConsumerExact.HelperTransport.square at hCall
  generalize hSource :
      V5FriHelperTransparent.square
        (V5FriConsumerExact.HelperTransport.toSourceQM31 input) = sourceResult
      at hCall
  cases sourceResult with
  | fail error =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
  | div =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
  | ok value =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
      subst output
      unfold V5FriHelperTransparent.square at hSource
      have hCanonicalSource :
          canonicalQM31
            (V5FriConsumerExact.HelperTransport.toSourceQM31 input) := by
        simpa using hCanonical
      have hSemantics :=
        source_square_success
          (V5FriConsumerExact.HelperTransport.toSourceQM31 input)
          value hCanonicalSource hSource
      simpa using hSemantics

theorem consumer_mul_semantics
    (left right output : AspisV5FriConsumerValueSemantics.Consumer.QM31)
    (hLeft :
      canonicalQM31 (AspisV5FriConsumerValueSemantics.toExactQM31 left))
    (hRight :
      canonicalQM31 (AspisV5FriConsumerValueSemantics.toExactQM31 right))
    (hCall :
      V5FriConsumerExact.aspis_core.field.QM31.mul left right = .ok output) :
    canonicalQM31 (AspisV5FriConsumerValueSemantics.toExactQM31 output) ∧
      qm31View (AspisV5FriConsumerValueSemantics.toExactQM31 output) =
        qm31View (AspisV5FriConsumerValueSemantics.toExactQM31 left) *
          qm31View (AspisV5FriConsumerValueSemantics.toExactQM31 right) := by
  unfold V5FriConsumerExact.aspis_core.field.QM31.mul
    V5FriConsumerExact.HelperTransport.mul at hCall
  generalize hSource :
      V5FriHelperTransparent.mul
        (V5FriConsumerExact.HelperTransport.toSourceQM31 left)
        (V5FriConsumerExact.HelperTransport.toSourceQM31 right) = sourceResult
      at hCall
  cases sourceResult with
  | fail error =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
  | div =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
  | ok value =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
      subst output
      unfold V5FriHelperTransparent.mul at hSource
      have hLeftSource :
          canonicalQM31
            (V5FriConsumerExact.HelperTransport.toSourceQM31 left) := by
        simpa using hLeft
      have hRightSource :
          canonicalQM31
            (V5FriConsumerExact.HelperTransport.toSourceQM31 right) := by
        simpa using hRight
      have hSemantics :=
        source_mul_success
          (V5FriConsumerExact.HelperTransport.toSourceQM31 left)
          (V5FriConsumerExact.HelperTransport.toSourceQM31 right)
          value hLeftSource hRightSource hSource
      simpa using hSemantics

theorem consumer_prepared_semantics
    (input : AspisV5FriConsumerValueSemantics.Consumer.QM31)
    (output : AspisV5FriConsumerValueSemantics.Consumer.Prepared)
    (hCanonical :
      canonicalQM31 (AspisV5FriConsumerValueSemantics.toExactQM31 input))
    (hCall :
      V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier.new input =
        .ok output) :
    PreparedRepresents
      (V5FriConsumerExact.HelperTransport.toArithmeticPrepared output)
      (qm31View (AspisV5FriConsumerValueSemantics.toExactQM31 input)) := by
  unfold V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier.new
    V5FriConsumerExact.HelperTransport.preparedNew at hCall
  generalize hSource :
      V5FriHelperTransparent.prepare
        (V5FriConsumerExact.HelperTransport.toSourceQM31 input) = sourceResult
      at hCall
  cases sourceResult with
  | fail error =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
  | div =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
  | ok value =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
      subst output
      unfold V5FriHelperTransparent.prepare at hSource
      have hCanonicalSource :
          canonicalQM31
            (V5FriConsumerExact.HelperTransport.toSourceQM31 input) := by
        simpa using hCanonical
      have hSemantics :=
        source_prepared_success
          (V5FriConsumerExact.HelperTransport.toSourceQM31 input)
          value hCanonicalSource hSource
      simpa using hSemantics

theorem consumer_circle_transport
    (values : Array AspisV5FriConsumerValueSemantics.Consumer.QM31 4#usize)
    (alphaPowers :
      Array AspisV5FriConsumerValueSemantics.Consumer.Prepared 3#usize)
    (inv2x inv2y : AspisV5FriConsumerValueSemantics.Consumer.M31)
    (output : AspisV5FriConsumerValueSemantics.Consumer.QM31)
    (hCall :
      V5FriConsumerExact.aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
          values alphaPowers inv2x inv2y = .ok output) :
    V5FriArithmeticExact.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
        (AspisV5FriConsumerValueSemantics.mapArray
          AspisV5FriConsumerValueSemantics.toExactQM31 values)
        (AspisV5FriConsumerValueSemantics.mapArray
          V5FriConsumerExact.HelperTransport.toArithmeticPrepared alphaPowers)
        inv2x inv2y =
      .ok (AspisV5FriConsumerValueSemantics.toExactQM31 output) := by
  unfold
    V5FriConsumerExact.aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
      at hCall
  rw [circle_transport_call] at hCall
  generalize hArithmetic :
      V5FriArithmeticExact.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
        (V5FriConsumerExact.HelperTransport.mapArray
          V5FriConsumerExact.HelperTransport.toArithmeticQM31 values)
        (V5FriConsumerExact.HelperTransport.mapArray
          V5FriConsumerExact.HelperTransport.toArithmeticPrepared alphaPowers)
        inv2x inv2y = arithmeticResult at hCall
  cases arithmeticResult with
  | fail error =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
  | div =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
  | ok value =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hCall
      subst output
      simpa using hArithmetic

theorem map_source_query_result_success
    {result :
      Result
        (core.result.Result Unit
          V5FriConsumerExact.HelperTransport.Source.CircleQueryError)}
    (hMapped :
      V5FriConsumerExact.HelperTransport.mapResult
          V5FriConsumerExact.HelperTransport.fromSourceQueryResult result =
        .ok (.Ok ())) :
    result = .ok (.Ok ()) := by
  cases result with
  | fail error =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hMapped
  | div =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hMapped
  | ok inner =>
      cases inner with
      | Err error =>
          simp [V5FriConsumerExact.HelperTransport.mapResult,
            V5FriConsumerExact.HelperTransport.fromSourceQueryResult] at hMapped
      | Ok unit =>
          cases unit
          rfl

theorem consumer_line_transport
    (incoming outgoing : Slice Std.U8) (index : Std.Usize)
    (layer : Std.U8)
    (inverses : Array AspisV5FriConsumerValueSemantics.Consumer.M31 3#usize)
    (alphaPowers :
      Array AspisV5FriConsumerValueSemantics.Consumer.Prepared 3#usize)
    (hCall :
      V5FriConsumerExact.aspis_core.circle_query.check_fixed_line_transition_prepared_polynomial_powers
          incoming outgoing index layer inverses alphaPowers = .ok (.Ok ())) :
    V5FriArithmeticExact.circle_query.check_fixed_line_transition_prepared_polynomial_powers
        incoming outgoing index layer inverses
        (AspisV5FriConsumerValueSemantics.mapArray
          V5FriConsumerExact.HelperTransport.toArithmeticPrepared alphaPowers) =
      .ok (.Ok ()) := by
  unfold
    V5FriConsumerExact.aspis_core.circle_query.check_fixed_line_transition_prepared_polynomial_powers
    V5FriConsumerExact.HelperTransport.line at hCall
  have hSource := map_source_query_result_success hCall
  unfold V5FriHelperTransparent.line at hSource
  rw [source_line_call_eq_arithmetic] at hSource
  simpa using hSource

theorem consumer_terminal_transport
    (incoming : Slice Std.U8)
    (finalPolynomial :
      Array AspisV5FriConsumerValueSemantics.Consumer.QM31 4#usize)
    (index : Std.Usize)
    (inverses : Array AspisV5FriConsumerValueSemantics.Consumer.M31 3#usize)
    (finalX : AspisV5FriConsumerValueSemantics.Consumer.M31)
    (alphaPowers :
      Array AspisV5FriConsumerValueSemantics.Consumer.Prepared 3#usize)
    (hCall :
      V5FriConsumerExact.aspis_core.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
          incoming finalPolynomial index inverses finalX alphaPowers =
        .ok (.Ok ())) :
    V5FriArithmeticExact.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
        incoming
        (AspisV5FriConsumerValueSemantics.mapArray
          AspisV5FriConsumerValueSemantics.toExactQM31 finalPolynomial)
        index inverses finalX
        (AspisV5FriConsumerValueSemantics.mapArray
          V5FriConsumerExact.HelperTransport.toArithmeticPrepared alphaPowers) =
      .ok (.Ok ()) := by
  unfold
    V5FriConsumerExact.aspis_core.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
    V5FriConsumerExact.HelperTransport.terminal at hCall
  have hSource := map_source_query_result_success hCall
  unfold V5FriHelperTransparent.terminal at hSource
  rw [source_terminal_call_eq_arithmetic] at hSource
  simpa using hSource

/-- The six calls used by the accepted V5 FRI consumer are the extracted Rust
calls proved above. No field, fold, decoder, line, or terminal helper remains
abstract in this record. -/
def transparentFriHelperCallEquality :
    AspisV5FriConsumerValueSemantics.ExactFriHelperCallEquality := {
  prepared := V5FriConsumerExact.HelperTransport.toArithmeticPrepared
  square := consumer_square_semantics
  mul := consumer_mul_semantics
  preparedNew := consumer_prepared_semantics
  circle := consumer_circle_transport
  line := consumer_line_transport
  terminal := consumer_terminal_transport
}

#print axioms transparentFriHelperCallEquality

end AspisV5FriTransparentHelperEquality
