import ComponentBV5EvaluateCurrent20260722
import CM31MultiplicativeProof
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Ring

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBRealEvaluatorProof

abbrev M31 := ComponentBGenerated.aspis_core.field.M31
abbrev QM31 := ComponentBGenerated.aspis_core.field.QM31

/-! ## Exact semantics of the generated QM31 operations

This bridge uses the single source-authentic multiplicative extraction already
proved in `CM31MultiplicativeProof`.  The generated MLE module owns distinct
CM31/QM31 structures, so the bridge is explicit at every coordinate; the M31
words themselves are definitionally the same `U32` type.
-/

abbrev GeneratedCM31 := ComponentBGenerated.aspis_core.field.CM31
abbrev ExactM31 := AspisAeneasCM31Exact.M31Exact
abbrev ExactCM31 := AspisAeneasCM31Exact.CM31Exact

def exactQm31R : ExactCM31 := ⟨2, 1⟩

abbrev ExactQM31 := QuadraticAlgebra ExactCM31 exactQm31R 0

def generatedCm31ToExact (x : GeneratedCM31) : ExactCM31 :=
  ⟨(x.a.val : ExactM31), (x.b.val : ExactM31)⟩

def generatedQm31ToExact (x : QM31) : ExactQM31 :=
  ⟨generatedCm31ToExact x.c0, generatedCm31ToExact x.c1⟩

def GeneratedCanonicalCM31 (x : GeneratedCM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 x.a.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 x.b.val

def GeneratedCanonicalQM31 (x : QM31) : Prop :=
  GeneratedCanonicalCM31 x.c0 ∧ GeneratedCanonicalCM31 x.c1

private theorem generated_P_eq_multiplicative :
    ComponentBGenerated.aspis_core.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold ComponentBGenerated.aspis_core.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem generated_reduce_u64_eq_multiplicative (x : Std.U64) :
    ComponentBGenerated.aspis_core.field.reduce_u64 x =
      AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  unfold ComponentBGenerated.aspis_core.field.reduce_u64
    AspisCoreCM31Multiplicative.field.reduce_u64
  rw [generated_P_eq_multiplicative]

private theorem generated_m31_add_eq_multiplicative (a b : M31) :
    ComponentBGenerated.aspis_core.field.M31.add a b =
      AspisCoreCM31Multiplicative.field.M31.add a b := by
  unfold ComponentBGenerated.aspis_core.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [generated_P_eq_multiplicative]

private theorem generated_m31_sub_eq_multiplicative (a b : M31) :
    ComponentBGenerated.aspis_core.field.M31.sub a b =
      AspisCoreCM31Multiplicative.field.M31.sub a b := by
  unfold ComponentBGenerated.aspis_core.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [generated_P_eq_multiplicative]

private theorem generated_m31_mul_eq_multiplicative (a b : M31) :
    ComponentBGenerated.aspis_core.field.M31.mul a b =
      AspisCoreCM31Multiplicative.field.M31.mul a b := by
  unfold ComponentBGenerated.aspis_core.field.M31.mul
    AspisCoreCM31Multiplicative.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [generated_reduce_u64_eq_multiplicative]

private theorem generated_m31_add_corresponds
    (a b : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : M31,
      ComponentBGenerated.aspis_core.field.M31.add a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) + (b.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds a b ha hb
  refine ⟨out, ?_, outputCanonical, outputExact⟩
  rw [generated_m31_add_eq_multiplicative]
  exact outputEquation

private theorem generated_m31_sub_corresponds
    (a b : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : M31,
      ComponentBGenerated.aspis_core.field.M31.sub a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) - (b.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds a b ha hb
  refine ⟨out, ?_, outputCanonical, outputExact⟩
  rw [generated_m31_sub_eq_multiplicative]
  exact outputEquation

private theorem generated_m31_mul_corresponds
    (a b : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val)
    (hb : AspisAeneasCM31Multiplicative.CanonicalRawM31 b.val) :
    ∃ out : M31,
      ComponentBGenerated.aspis_core.field.M31.mul a b = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) * (b.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds a b ha hb
  refine ⟨out, ?_, outputCanonical, outputExact⟩
  rw [generated_m31_mul_eq_multiplicative]
  exact outputEquation

private theorem generated_m31_double_corresponds
    (a : M31)
    (ha : AspisAeneasCM31Multiplicative.CanonicalRawM31 a.val) :
    ∃ out : M31,
      ComponentBGenerated.aspis_core.field.M31.double a = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) =
        (a.val : ExactM31) + (a.val : ExactM31) := by
  obtain ⟨out, outputEquation, outputCanonical, outputExact⟩ :=
    generated_m31_add_corresponds a a ha ha
  exact ⟨out, outputEquation, outputCanonical, outputExact⟩

private theorem generated_cm31_add_corresponds
    (x y : GeneratedCM31)
    (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : GeneratedCM31,
      ComponentBGenerated.aspis_core.field.CM31.add x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        generatedCm31ToExact x + generatedCm31ToExact y := by
  obtain ⟨oa, hcallA, hcanA, hexactA⟩ :=
    generated_m31_add_corresponds x.a y.a hx.1 hy.1
  obtain ⟨ob, hcallB, hcanB, hexactB⟩ :=
    generated_m31_add_corresponds x.b y.b hx.2 hy.2
  let out : GeneratedCM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.CM31.add, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem generated_cm31_sub_corresponds
    (x y : GeneratedCM31)
    (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : GeneratedCM31,
      ComponentBGenerated.aspis_core.field.CM31.sub x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        generatedCm31ToExact x - generatedCm31ToExact y := by
  obtain ⟨oa, hcallA, hcanA, hexactA⟩ :=
    generated_m31_sub_corresponds x.a y.a hx.1 hy.1
  obtain ⟨ob, hcallB, hcanB, hexactB⟩ :=
    generated_m31_sub_corresponds x.b y.b hx.2 hy.2
  let out : GeneratedCM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.CM31.sub, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem generated_cm31_mul_corresponds
    (x y : GeneratedCM31)
    (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : GeneratedCM31,
      ComponentBGenerated.aspis_core.field.CM31.mul x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        generatedCm31ToExact x * generatedCm31ToExact y := by
  obtain ⟨m0, hm0, hm0Canonical, hm0Exact⟩ :=
    generated_m31_mul_corresponds x.a y.a hx.1 hy.1
  obtain ⟨m1, hm1, hm1Canonical, hm1Exact⟩ :=
    generated_m31_mul_corresponds x.b y.b hx.2 hy.2
  obtain ⟨xsum, hxsum, hxsumCanonical, hxsumExact⟩ :=
    generated_m31_add_corresponds x.a x.b hx.1 hx.2
  obtain ⟨ysum, hysum, hysumCanonical, hysumExact⟩ :=
    generated_m31_add_corresponds y.a y.b hy.1 hy.2
  obtain ⟨m2, hm2, hm2Canonical, hm2Exact⟩ :=
    generated_m31_mul_corresponds xsum ysum hxsumCanonical hysumCanonical
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_m31_sub_corresponds m0 m1 hm0Canonical hm1Canonical
  obtain ⟨imagPartial, himagPartial, himagPartialCanonical,
      himagPartialExact⟩ :=
    generated_m31_sub_corresponds m2 m0 hm2Canonical hm0Canonical
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_m31_sub_corresponds imagPartial m1
      himagPartialCanonical hm1Canonical
  have realExact :
      ((real.val : Nat) : ExactM31) =
        (x.a.val : ExactM31) * (y.a.val : ExactM31) -
          (x.b.val : ExactM31) * (y.b.val : ExactM31) := by
    rw [hrealExact, hm0Exact, hm1Exact]
  have imagExact :
      ((imag.val : Nat) : ExactM31) =
        (x.a.val : ExactM31) * (y.b.val : ExactM31) +
          (x.b.val : ExactM31) * (y.a.val : ExactM31) := by
    calc
      ((imag.val : Nat) : ExactM31) =
          ((imagPartial.val : Nat) : ExactM31) -
            ((m1.val : Nat) : ExactM31) := himagExact
      _ = (((m2.val : Nat) : ExactM31) -
            ((m0.val : Nat) : ExactM31)) -
            ((m1.val : Nat) : ExactM31) := by rw [himagPartialExact]
      _ = (((x.a.val : ExactM31) + (x.b.val : ExactM31)) *
            ((y.a.val : ExactM31) + (y.b.val : ExactM31)) -
            (x.a.val : ExactM31) * (y.a.val : ExactM31)) -
            (x.b.val : ExactM31) * (y.b.val : ExactM31) := by
          rw [hm2Exact, hxsumExact, hysumExact, hm0Exact, hm1Exact]
      _ = (x.a.val : ExactM31) * (y.b.val : ExactM31) +
            (x.b.val : ExactM31) * (y.a.val : ExactM31) := by ring
  let out : GeneratedCM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.CM31.mul, hm0, hm1,
      hxsum, hysum, hm2, hreal, himagPartial, himag, out]
  · apply QuadraticAlgebra.ext
    · simpa [generatedCm31ToExact, sub_eq_add_neg] using realExact
    · simpa [generatedCm31ToExact] using imagExact

private theorem generated_mul_by_r_corresponds
    (x : GeneratedCM31) (hx : GeneratedCanonicalCM31 x) :
    ∃ out : GeneratedCM31,
      ComponentBGenerated.aspis_core.field.mul_by_r x = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out = generatedCm31ToExact x * exactQm31R := by
  obtain ⟨doubleA, hdoubleA, hdoubleACanonical, hdoubleAExact⟩ :=
    generated_m31_add_corresponds x.a x.a hx.1 hx.1
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_m31_sub_corresponds doubleA x.b hdoubleACanonical hx.2
  obtain ⟨doubleB, hdoubleB, hdoubleBCanonical, hdoubleBExact⟩ :=
    generated_m31_add_corresponds x.b x.b hx.2 hx.2
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_m31_add_corresponds x.a doubleB hx.1 hdoubleBCanonical
  let out : GeneratedCM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.mul_by_r,
      ComponentBGenerated.aspis_core.field.M31.double,
      hdoubleA, hreal, hdoubleB, himag, out]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) =
        (generatedCm31ToExact x * exactQm31R).re
      rw [hrealExact, hdoubleAExact]
      simp [generatedCm31ToExact, exactQm31R]
      ring
    · change ((imag.val : Nat) : ExactM31) =
        (generatedCm31ToExact x * exactQm31R).im
      rw [himagExact, hdoubleBExact]
      simp [generatedCm31ToExact, exactQm31R]
      ring

theorem generated_qm31_add_corresponds
    (x y : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y) :
    ∃ out : QM31,
      ComponentBGenerated.aspis_core.field.QM31.add x y = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x + generatedQm31ToExact y := by
  obtain ⟨o0, hcall0, hcan0, hexact0⟩ :=
    generated_cm31_add_corresponds x.c0 y.c0 hx.1 hy.1
  obtain ⟨o1, hcall1, hcan1, hexact1⟩ :=
    generated_cm31_add_corresponds x.c1 y.c1 hx.2 hy.2
  let out : QM31 := ⟨o0, o1⟩
  refine ⟨out, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.QM31.add, hcall0, hcall1, out]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

theorem generated_qm31_mul_corresponds
    (x y : QM31) (hx : GeneratedCanonicalQM31 x)
    (hy : GeneratedCanonicalQM31 y) :
    ∃ out : QM31,
      ComponentBGenerated.aspis_core.field.QM31.mul x y = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact x * generatedQm31ToExact y := by
  obtain ⟨m0, hm0, hm0Canonical, hm0Exact⟩ :=
    generated_cm31_mul_corresponds x.c0 y.c0 hx.1 hy.1
  obtain ⟨m1, hm1, hm1Canonical, hm1Exact⟩ :=
    generated_cm31_mul_corresponds x.c1 y.c1 hx.2 hy.2
  obtain ⟨xsum, hxsum, hxsumCanonical, hxsumExact⟩ :=
    generated_cm31_add_corresponds x.c0 x.c1 hx.1 hx.2
  obtain ⟨ysum, hysum, hysumCanonical, hysumExact⟩ :=
    generated_cm31_add_corresponds y.c0 y.c1 hy.1 hy.2
  obtain ⟨m2, hm2, hm2Canonical, hm2Exact⟩ :=
    generated_cm31_mul_corresponds xsum ysum hxsumCanonical hysumCanonical
  obtain ⟨rm1, hrm1, hrm1Canonical, hrm1Exact⟩ :=
    generated_mul_by_r_corresponds m1 hm1Canonical
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_cm31_add_corresponds m0 rm1 hm0Canonical hrm1Canonical
  obtain ⟨crossPartial, hcrossPartial, hcrossPartialCanonical,
      hcrossPartialExact⟩ :=
    generated_cm31_sub_corresponds m2 m0 hm2Canonical hm0Canonical
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_cm31_sub_corresponds crossPartial m1
      hcrossPartialCanonical hm1Canonical
  let out : QM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.QM31.mul, hm0, hm1,
      hxsum, hysum, hm2, hrm1, hreal, hcrossPartial, himag, out]
  · apply QuadraticAlgebra.ext
    · change generatedCm31ToExact real =
        (generatedQm31ToExact x * generatedQm31ToExact y).re
      rw [hrealExact, hm0Exact, hrm1Exact, hm1Exact]
      simp [generatedQm31ToExact]
      ring
    · change generatedCm31ToExact imag =
        (generatedQm31ToExact x * generatedQm31ToExact y).im
      rw [himagExact, hcrossPartialExact, hm2Exact, hxsumExact,
        hysumExact, hm0Exact, hm1Exact]
      simp [generatedQm31ToExact]
      ring

private def RepresentsPreparedRow
    (row : Array M31 3#usize) (x : GeneratedCM31) : Prop :=
  ∃ sum : M31,
    ComponentBGenerated.aspis_core.field.M31.add x.a x.b = ok sum ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 sum.val ∧
    row.val = [x.a, x.b, sum]

private def RepresentsPrepared
    (prepared : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier)
    (left : QM31) : Prop :=
  ∃ leftSum : GeneratedCM31,
  ∃ row0 row1 row2 : Array M31 3#usize,
    ComponentBGenerated.aspis_core.field.CM31.add left.c0 left.c1 = ok leftSum ∧
    GeneratedCanonicalCM31 leftSum ∧
    RepresentsPreparedRow row0 left.c0 ∧
    RepresentsPreparedRow row1 left.c1 ∧
    RepresentsPreparedRow row2 leftSum ∧
    prepared.components.val = [row0, row1, row2]

private theorem preparedRowExists
    (x : GeneratedCM31) (hx : GeneratedCanonicalCM31 x) :
    ∃ row : Array M31 3#usize,
      ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
          () x = ok row ∧
      RepresentsPreparedRow row x := by
  obtain ⟨sum, hsum, hsumCanonical, _⟩ :=
    generated_m31_add_corresponds x.a x.b hx.1 hx.2
  let row : Array M31 3#usize := Array.make 3#usize [x.a, x.b, sum]
  refine ⟨row, ?_, ⟨sum, hsum, hsumCanonical, rfl⟩⟩
  simp [ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    hsum, row]

private theorem generatedPreparedNewRepresents
    (left : QM31) (hleft : GeneratedCanonicalQM31 left) :
    ∃ prepared : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier,
      ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.new left =
        ok prepared ∧
      RepresentsPrepared prepared left := by
  obtain ⟨row0, hrow0Call, hrow0⟩ := preparedRowExists left.c0 hleft.1
  obtain ⟨row1, hrow1Call, hrow1⟩ := preparedRowExists left.c1 hleft.2
  obtain ⟨leftSum, hleftSum, hleftSumCanonical, _⟩ :=
    generated_cm31_add_corresponds left.c0 left.c1 hleft.1 hleft.2
  obtain ⟨row2, hrow2Call, hrow2⟩ :=
    preparedRowExists leftSum hleftSumCanonical
  let prepared : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier :=
    ⟨Array.make 3#usize [row0, row1, row2]⟩
  refine ⟨prepared, ?_, ⟨leftSum, row0, row1, row2, hleftSum,
    hleftSumCanonical, hrow0, hrow1, hrow2, rfl⟩⟩
  simp [ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.new,
    hrow0Call, hrow1Call, hleftSum, hrow2Call, prepared]

private theorem preparedRowCallEqCm31Mul
    (row : Array M31 3#usize) (left right : GeneratedCM31)
    (hrow : RepresentsPreparedRow row left) :
    ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (row, right) =
      ComponentBGenerated.aspis_core.field.CM31.mul left right := by
  obtain ⟨sum, hsum, _, hrowVal⟩ := hrow
  simp [ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
    ComponentBGenerated.aspis_core.field.CM31.mul, Array.index_usize,
    hrowVal, hsum]

private theorem representedPreparedMulEqQm31Mul
    (prepared : ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier)
    (left right : QM31) (hprepared : RepresentsPrepared prepared left) :
    ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul
        prepared right =
      ComponentBGenerated.aspis_core.field.QM31.mul left right := by
  obtain ⟨leftSum, row0, row1, row2, hleftSum, _, hrow0, hrow1,
      hrow2, hcomponents⟩ := hprepared
  have hcomponent0 : Array.index_usize prepared.components 0#usize = ok row0 := by
    simp [Array.index_usize, hcomponents]
  have hcomponent1 : Array.index_usize prepared.components 1#usize = ok row1 := by
    simp [Array.index_usize, hcomponents]
  have hcomponent2 : Array.index_usize prepared.components 2#usize = ok row2 := by
    simp [Array.index_usize, hcomponents]
  unfold ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul
  rw [hcomponent0, hcomponent1, hcomponent2]
  simp only [bind_tc_ok]
  rw [preparedRowCallEqCm31Mul row0 left.c0 right.c0 hrow0]
  rw [preparedRowCallEqCm31Mul row1 left.c1 right.c1 hrow1]
  simp_rw [preparedRowCallEqCm31Mul row2 leftSum _ hrow2]
  unfold ComponentBGenerated.aspis_core.field.QM31.mul
  rw [hleftSum]
  simp only [bind_tc_ok]

/-- The authentic generated prepared constructor and multiply body together
denote ordinary exact QM31 multiplication.  The cache representation is
proved internally, rather than assumed by this theorem. -/
theorem generated_prepared_new_mul_corresponds
    (left : QM31) (hleft : GeneratedCanonicalQM31 left) :
    ∃ prepared,
      ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.new left =
        ok prepared ∧
      ∀ right, GeneratedCanonicalQM31 right →
        ∃ out,
          ComponentBGenerated.aspis_core.field.PreparedQm31Multiplier.mul
              prepared right = ok out ∧
          GeneratedCanonicalQM31 out ∧
          generatedQm31ToExact out =
            generatedQm31ToExact left * generatedQm31ToExact right := by
  obtain ⟨prepared, hnew, hrep⟩ := generatedPreparedNewRepresents left hleft
  refine ⟨prepared, hnew, ?_⟩
  intro right hright
  rw [representedPreparedMulEqQm31Mul prepared left right hrep]
  exact generated_qm31_mul_corresponds left right hleft hright

private theorem generated_cm31_square_corresponds
    (x : GeneratedCM31) (hx : GeneratedCanonicalCM31 x) :
    ∃ out : GeneratedCM31,
      ComponentBGenerated.aspis_core.field.CM31.square x = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out = generatedCm31ToExact x ^ 2 := by
  obtain ⟨sum, hsum, hsumCanonical, hsumExact⟩ :=
    generated_m31_add_corresponds x.a x.b hx.1 hx.2
  obtain ⟨difference, hdifference, hdifferenceCanonical,
      hdifferenceExact⟩ :=
    generated_m31_sub_corresponds x.a x.b hx.1 hx.2
  obtain ⟨real, hreal, hrealCanonical, hrealExact⟩ :=
    generated_m31_mul_corresponds sum difference
      hsumCanonical hdifferenceCanonical
  obtain ⟨product, hproduct, hproductCanonical, hproductExact⟩ :=
    generated_m31_mul_corresponds x.a x.b hx.1 hx.2
  obtain ⟨imag, himag, himagCanonical, himagExact⟩ :=
    generated_m31_double_corresponds product hproductCanonical
  have himagAdd :
      ComponentBGenerated.aspis_core.field.M31.add product product = ok imag := by
    simpa [ComponentBGenerated.aspis_core.field.M31.double] using himag
  let out : GeneratedCM31 := ⟨real, imag⟩
  refine ⟨out, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.CM31.square,
      ComponentBGenerated.aspis_core.field.M31.double, hsum, hdifference,
      hreal, hproduct, himagAdd, out]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) =
        (generatedCm31ToExact x ^ 2).re
      rw [hrealExact, hsumExact, hdifferenceExact]
      simp [pow_two, generatedCm31ToExact]
      ring
    · change ((imag.val : Nat) : ExactM31) =
        (generatedCm31ToExact x ^ 2).im
      rw [himagExact, hproductExact]
      simp [pow_two, generatedCm31ToExact]
      ring

/-- The specialized square body in the authentic combined evaluator
extraction preserves canonical limbs and denotes exact squaring. -/
theorem generated_qm31_square_corresponds
    (x : QM31) (hx : GeneratedCanonicalQM31 x) :
    ∃ out : QM31,
      ComponentBGenerated.aspis_core.field.QM31.square x = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = generatedQm31ToExact x ^ 2 := by
  obtain ⟨c0Square, hc0Square, hc0SquareCanonical, hc0SquareExact⟩ :=
    generated_cm31_square_corresponds x.c0 hx.1
  obtain ⟨c1Square, hc1Square, hc1SquareCanonical, hc1SquareExact⟩ :=
    generated_cm31_square_corresponds x.c1 hx.2
  obtain ⟨rTimesC1Square, hrTimesC1Square, hrTimesC1SquareCanonical,
      hrTimesC1SquareExact⟩ :=
    generated_mul_by_r_corresponds c1Square hc1SquareCanonical
  obtain ⟨low, hlow, hlowCanonical, hlowExact⟩ :=
    generated_cm31_add_corresponds c0Square rTimesC1Square
      hc0SquareCanonical hrTimesC1SquareCanonical
  obtain ⟨cross, hcross, hcrossCanonical, hcrossExact⟩ :=
    generated_cm31_mul_corresponds x.c0 x.c1 hx.1 hx.2
  obtain ⟨high, hhigh, hhighCanonical, hhighExact⟩ :=
    generated_cm31_add_corresponds cross cross hcrossCanonical hcrossCanonical
  let out : QM31 := ⟨low, high⟩
  refine ⟨out, ?_, ⟨hlowCanonical, hhighCanonical⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.QM31.square,
      ComponentBGenerated.aspis_core.field.CM31.double, hc0Square,
      hc1Square, hrTimesC1Square, hlow, hcross, hhigh, out]
  · apply QuadraticAlgebra.ext
    · change generatedCm31ToExact low =
        (generatedQm31ToExact x ^ 2).re
      rw [hlowExact, hc0SquareExact, hrTimesC1SquareExact,
        hc1SquareExact]
      simp only [pow_two, QuadraticAlgebra.re_mul, generatedQm31ToExact]
      ring
    · change generatedCm31ToExact high =
        (generatedQm31ToExact x ^ 2).im
      rw [hhighExact, hcrossExact]
      simp [pow_two, generatedQm31ToExact]
      ring

#print axioms generated_qm31_add_corresponds
#print axioms generated_qm31_mul_corresponds
#print axioms generated_prepared_new_mul_corresponds
#print axioms generated_qm31_square_corresponds

end ComponentBRealEvaluatorProof
