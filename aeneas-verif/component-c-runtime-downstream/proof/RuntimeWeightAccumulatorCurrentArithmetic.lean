import RuntimeEvaluatorCanonicalCurrent20260722
import HalfProof
import QM31MulProof
import AspisFormal.V5ComponentCQM31TowerExact

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace ComponentCRuntimeCanonicalGenerated.RuntimeWeightAccumulatorCurrentArithmetic

open ComponentCRuntimeCanonicalGenerated

abbrev RawM31 := aspis_core.field.M31
abbrev RawCM31 := aspis_core.field.CM31
abbrev RawQM31 := aspis_core.field.QM31
abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExactCM31 := AspisV5ComponentCQM31TowerExact.CM31Exact
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def CanonicalM31 (x : RawM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 x.val

def CanonicalCM31 (x : RawCM31) : Prop :=
  CanonicalM31 x.a ∧ CanonicalM31 x.b

def CanonicalQM31 (x : RawQM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

def cm31View (x : RawCM31) : ExactCM31 :=
  ⟨(x.a.val : ExactM31), (x.b.val : ExactM31)⟩

def qm31View (x : RawQM31) : ExactQM31 :=
  ⟨cm31View x.c0, cm31View x.c1⟩

private theorem current_P_eq_half :
    aspis_core.field.P = AspisCoreHalf.field.P := by
  apply UScalar.eq_of_val_eq
  unfold aspis_core.field.P AspisCoreHalf.field.P
  rfl

private theorem current_m31_half_eq_half (x : RawM31) :
    aspis_core.field.M31.half x = AspisCoreHalf.field.M31.half x := by
  unfold aspis_core.field.M31.half AspisCoreHalf.field.M31.half
  rw [current_P_eq_half]
  simp only [halfShiftCountOne_exact]

theorem current_qm31_half_corresponds
    (x : RawQM31) (hx : CanonicalQM31 x) :
    ∃ out,
      aspis_core.field.QM31.half x = ok out ∧
      CanonicalQM31 out ∧
      qm31View out + qm31View out = qm31View x := by
  have m31_half (v : RawM31) (hv : CanonicalM31 v) :
      ∃ out,
        aspis_core.field.M31.half v = ok out ∧
        CanonicalM31 out ∧
        ((out.val : Nat) : ExactM31) + (out.val : ExactM31) =
          (v.val : ExactM31) := by
    rcases AspisAeneasHalf.extracted_m31_half_corresponds v hv with
      ⟨out, hcall, _hraw, hcan, hview⟩
    refine ⟨out, ?_, hcan, ?_⟩
    · rw [current_m31_half_eq_half]
      exact hcall
    · have htwo : (2 : ExactM31) ≠ 0 := by decide
      rw [← mul_two]
      exact (eq_div_iff htwo).1 hview
  have cm31_half (v : RawCM31) (hv : CanonicalCM31 v) :
      ∃ out,
        aspis_core.field.CM31.half v = ok out ∧
        CanonicalCM31 out ∧
        cm31View out + cm31View out = cm31View v := by
    rcases m31_half v.a hv.1 with ⟨oa, ha, hca, hva⟩
    rcases m31_half v.b hv.2 with ⟨ob, hb, hcb, hvb⟩
    refine ⟨⟨oa, ob⟩, ?_, ⟨hca, hcb⟩, ?_⟩
    · simp [aspis_core.field.CM31.half, ha, hb]
    · apply QuadraticAlgebra.ext
      · exact hva
      · exact hvb
  rcases cm31_half x.c0 hx.1 with ⟨o0, h0, hc0, hv0⟩
  rcases cm31_half x.c1 hx.2 with ⟨o1, h1, hc1, hv1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hc0, hc1⟩, ?_⟩
  · simp [aspis_core.field.QM31.half, h0, h1]
  · apply QuadraticAlgebra.ext
    · exact hv0
    · exact hv1

private theorem current_m31_add_eq_mul (x y : RawM31) :
    aspis_core.field.M31.add x y =
      AspisCoreCM31Multiplicative.field.M31.add x y := by
  simp [aspis_core.field.M31.add, aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.M31.add,
    AspisCoreCM31Multiplicative.field.P, Std.lift]

private theorem current_m31_sub_eq_mul (x y : RawM31) :
    aspis_core.field.M31.sub x y =
      AspisCoreCM31Multiplicative.field.M31.sub x y := by
  simp [aspis_core.field.M31.sub, aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.M31.sub,
    AspisCoreCM31Multiplicative.field.P, Std.lift]

private theorem current_reduce_u64_eq_mul (x : Std.U64) :
    aspis_core.field.reduce_u64 x =
      AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  simp [aspis_core.field.reduce_u64, aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.reduce_u64,
    AspisCoreCM31Multiplicative.field.P, Std.lift]

private theorem current_m31_mul_eq_mul (x y : RawM31) :
    aspis_core.field.M31.mul x y =
      AspisCoreCM31Multiplicative.field.M31.mul x y := by
  simp [aspis_core.field.M31.mul,
    AspisCoreCM31Multiplicative.field.M31.mul,
    current_reduce_u64_eq_mul, Std.lift]

private theorem current_m31_add_corresponds
    (x y : RawM31) (hx : CanonicalM31 x) (hy : CanonicalM31 y) :
    ∃ out,
      aspis_core.field.M31.add x y = ok out ∧ CanonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) + (y.val : ExactM31) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x y hx hy with ⟨out, hcall, hcan, hview⟩
  refine ⟨out, ?_, hcan, hview⟩
  rw [current_m31_add_eq_mul]
  exact hcall

private theorem current_m31_sub_corresponds
    (x y : RawM31) (hx : CanonicalM31 x) (hy : CanonicalM31 y) :
    ∃ out,
      aspis_core.field.M31.sub x y = ok out ∧ CanonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) - (y.val : ExactM31) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      x y hx hy with ⟨out, hcall, hcan, hview⟩
  refine ⟨out, ?_, hcan, hview⟩
  rw [current_m31_sub_eq_mul]
  exact hcall

private theorem current_m31_mul_corresponds
    (x y : RawM31) (hx : CanonicalM31 x) (hy : CanonicalM31 y) :
    ∃ out,
      aspis_core.field.M31.mul x y = ok out ∧ CanonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) * (y.val : ExactM31) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      x y hx hy with ⟨out, hcall, hcan, hview⟩
  refine ⟨out, ?_, hcan, hview⟩
  rw [current_m31_mul_eq_mul]
  exact hcall

private theorem current_cm31_add_corresponds
    (x y : RawCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out,
      aspis_core.field.CM31.add x y = ok out ∧ CanonicalCM31 out ∧
      cm31View out = cm31View x + cm31View y := by
  rcases current_m31_add_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, ha, hca, hva⟩
  rcases current_m31_add_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hb, hcb, hvb⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hca, hcb⟩, ?_⟩
  · simp [aspis_core.field.CM31.add, ha, hb]
  · apply QuadraticAlgebra.ext
    · exact hva
    · exact hvb

private theorem current_cm31_sub_corresponds
    (x y : RawCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out,
      aspis_core.field.CM31.sub x y = ok out ∧ CanonicalCM31 out ∧
      cm31View out = cm31View x - cm31View y := by
  rcases current_m31_sub_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, ha, hca, hva⟩
  rcases current_m31_sub_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hb, hcb, hvb⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hca, hcb⟩, ?_⟩
  · simp [aspis_core.field.CM31.sub, ha, hb]
  · apply QuadraticAlgebra.ext
    · exact hva
    · exact hvb

private theorem current_cm31_mul_corresponds
    (x y : RawCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out,
      aspis_core.field.CM31.mul x y = ok out ∧ CanonicalCM31 out ∧
      cm31View out = cm31View x * cm31View y := by
  rcases current_m31_mul_corresponds x.a y.a hx.1 hy.1 with
    ⟨m0, hm0, hc0, hv0⟩
  rcases current_m31_mul_corresponds x.b y.b hx.2 hy.2 with
    ⟨m1, hm1, hc1, hv1⟩
  rcases current_m31_add_corresponds x.a x.b hx.1 hx.2 with
    ⟨sx, hsx, hcsx, hvsx⟩
  rcases current_m31_add_corresponds y.a y.b hy.1 hy.2 with
    ⟨sy, hsy, hcsy, hvsy⟩
  rcases current_m31_mul_corresponds sx sy hcsx hcsy with
    ⟨m2, hm2, hc2, hv2⟩
  rcases current_m31_sub_corresponds m0 m1 hc0 hc1 with
    ⟨real, hr, hcr, hvr⟩
  rcases current_m31_sub_corresponds m2 m0 hc2 hc0 with
    ⟨mid, hmid, hcmid, hvmid⟩
  rcases current_m31_sub_corresponds mid m1 hcmid hc1 with
    ⟨imag, hi, hci, hvi⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hcr, hci⟩, ?_⟩
  · simp [aspis_core.field.CM31.mul, hm0, hm1, hsx, hsy, hm2,
      hr, hmid, hi]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) = (cm31View x * cm31View y).re
      rw [hvr, hv0, hv1]
      simp [cm31View]
      ring_nf
    · change ((imag.val : Nat) : ExactM31) = (cm31View x * cm31View y).im
      rw [hvi, hvmid, hv2, hvsx, hvsy, hv0, hv1]
      simp [cm31View]
      ring

private theorem current_mul_by_r_corresponds
    (x : RawCM31) (hx : CanonicalCM31 x) :
    ∃ out,
      aspis_core.field.mul_by_r x = ok out ∧ CanonicalCM31 out ∧
      cm31View out = cm31View x * AspisAeneasQM31Mul.qm31R := by
  rcases current_m31_add_corresponds x.a x.a hx.1 hx.1 with
    ⟨twoA, htwoA, hca, hva⟩
  rcases current_m31_sub_corresponds twoA x.b hca hx.2 with
    ⟨real, hr, hcr, hvr⟩
  rcases current_m31_add_corresponds x.b x.b hx.2 hx.2 with
    ⟨twoB, htwoB, hcb, hvb⟩
  rcases current_m31_add_corresponds x.a twoB hx.1 hcb with
    ⟨imag, hi, hci, hvi⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hcr, hci⟩, ?_⟩
  · simp [aspis_core.field.mul_by_r, aspis_core.field.M31.double,
      htwoA, hr, htwoB, hi]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) =
        (cm31View x * AspisAeneasQM31Mul.qm31R).re
      rw [hvr, hva]
      simp [cm31View, AspisAeneasQM31Mul.qm31R]
      ring
    · change ((imag.val : Nat) : ExactM31) =
        (cm31View x * AspisAeneasQM31Mul.qm31R).im
      rw [hvi, hvb]
      simp [cm31View, AspisAeneasQM31Mul.qm31R]
      ring

theorem current_qm31_add_corresponds
    (x y : RawQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out,
      aspis_core.field.QM31.add x y = ok out ∧ CanonicalQM31 out ∧
      qm31View out = qm31View x + qm31View y := by
  rcases current_cm31_add_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨o0, h0, hc0, hv0⟩
  rcases current_cm31_add_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨o1, h1, hc1, hv1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hc0, hc1⟩, ?_⟩
  · simp [aspis_core.field.QM31.add, h0, h1]
  · apply QuadraticAlgebra.ext
    · exact hv0
    · exact hv1

theorem current_qm31_mul_corresponds
    (x y : RawQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out,
      aspis_core.field.QM31.mul x y = ok out ∧ CanonicalQM31 out ∧
      qm31View out = qm31View x * qm31View y := by
  rcases current_cm31_mul_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨m0, hm0, hc0, hv0⟩
  rcases current_cm31_mul_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨m1, hm1, hc1, hv1⟩
  rcases current_cm31_add_corresponds x.c0 x.c1 hx.1 hx.2 with
    ⟨sx, hsx, hcsx, hvsx⟩
  rcases current_cm31_add_corresponds y.c0 y.c1 hy.1 hy.2 with
    ⟨sy, hsy, hcsy, hvsy⟩
  rcases current_cm31_mul_corresponds sx sy hcsx hcsy with
    ⟨m2, hm2, hc2, hv2⟩
  rcases current_mul_by_r_corresponds m1 hc1 with
    ⟨rm1, hrm1, hcrm1, hvrm1⟩
  rcases current_cm31_add_corresponds m0 rm1 hc0 hcrm1 with
    ⟨low, hlow, hclow, hvlow⟩
  rcases current_cm31_sub_corresponds m2 m0 hc2 hc0 with
    ⟨mid, hmid, hcmid, hvmid⟩
  rcases current_cm31_sub_corresponds mid m1 hcmid hc1 with
    ⟨high, hhigh, hchigh, hvhigh⟩
  have hR : AspisAeneasQM31Mul.qm31R =
      AspisV5ComponentCQM31TowerExact.qm31R := by rfl
  rw [hR] at hvrm1
  refine ⟨⟨low, high⟩, ?_, ⟨hclow, hchigh⟩, ?_⟩
  · simp [aspis_core.field.QM31.mul, hm0, hm1, hsx, hsy, hm2,
      hrm1, hlow, hmid, hhigh]
  · apply QuadraticAlgebra.ext
    · change cm31View low = (qm31View x * qm31View y).re
      rw [hvlow, hv0, hvrm1, hv1]
      simp [qm31View]
      ring
    · change cm31View high = (qm31View x * qm31View y).im
      rw [hvhigh, hvmid, hv2, hvsx, hvsy, hv0, hv1]
      simp [qm31View]
      ring

theorem current_qm31_zero_canonical :
    CanonicalQM31 aspis_core.field.QM31.ZERO := by
  norm_num [CanonicalQM31, CanonicalCM31, CanonicalM31,
    aspis_core.field.QM31.ZERO,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

theorem current_qm31_zero_view :
    qm31View aspis_core.field.QM31.ZERO = 0 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [qm31View, cm31View, aspis_core.field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;>
      simp [qm31View, cm31View, aspis_core.field.QM31.ZERO]

#print axioms current_qm31_half_corresponds
#print axioms current_qm31_add_corresponds
#print axioms current_qm31_mul_corresponds
#print axioms current_qm31_zero_canonical
#print axioms current_qm31_zero_view

end ComponentCRuntimeCanonicalGenerated.RuntimeWeightAccumulatorCurrentArithmetic
