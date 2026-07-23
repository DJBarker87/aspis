import RuntimeFoldPrimitiveReduction
import HalfProof
import QM31MulProof
import AspisFormal.V5M31RawSubNeg

set_option autoImplicit false

/-!
# Exact instantiation of the Component-C fold primitive interface

This file transfers the independently authenticated source extraction of the
shared field primitives into the full Component-C evaluator extraction.  The
two generated modules use different namespaces but the same Rust source; the
adapters below are literal coordinate maps, and each call equality is proved
inside Lean.
-/

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeFoldPrimitiveInstantiation

open aspis_prover
open ComponentCRuntimeFoldPrimitiveReduction

abbrev RuntimeM31 := aspis_prover.aspis_core.field.M31
abbrev RuntimeCM31 := aspis_prover.aspis_core.field.CM31
abbrev RuntimeQM31 := aspis_prover.aspis_core.field.QM31
abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExactCM31 := AspisV5ComponentCQM31TowerExact.CM31Exact
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def runtimeCanonicalM31 (x : RuntimeM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 x.val

def runtimeCanonicalCM31 (x : RuntimeCM31) : Prop :=
  runtimeCanonicalM31 x.a ∧ runtimeCanonicalM31 x.b

def runtimeCanonicalQM31 (x : RuntimeQM31) : Prop :=
  runtimeCanonicalCM31 x.c0 ∧ runtimeCanonicalCM31 x.c1

def runtimeM31View (x : RuntimeM31) : ExactQM31 :=
  ⟨⟨(x.val : ExactM31), 0⟩, 0⟩

def runtimeM31CMView (x : RuntimeM31) : ExactCM31 :=
  ⟨(x.val : ExactM31), 0⟩

def runtimeCM31View (x : RuntimeCM31) : ExactCM31 :=
  ⟨(x.a.val : ExactM31), (x.b.val : ExactM31)⟩

def runtimeQM31View (x : RuntimeQM31) : ExactQM31 :=
  ⟨runtimeCM31View x.c0, runtimeCM31View x.c1⟩

def mapResult {A B : Type*} (f : A → B) : Result A → Result B
  | ok x => ok (f x)
  | fail error => fail error
  | div => div

theorem runtime_m31_half_call_eq (x : RuntimeM31) :
    aspis_prover.aspis_core.field.M31.half x =
      AspisCoreHalf.field.M31.half x := by
  have hP : aspis_prover.aspis_core.field.P = AspisCoreHalf.field.P := by
    apply UScalar.eq_of_val_eq
    unfold aspis_prover.aspis_core.field.P AspisCoreHalf.field.P
    rfl
  unfold aspis_prover.aspis_core.field.M31.half AspisCoreHalf.field.M31.half
  simp only [Std.lift, bind_tc_ok]
  rw [hP, halfShiftCountOne_exact]

theorem runtime_m31_half_corresponds
    (x : RuntimeM31) (hx : runtimeCanonicalM31 x) :
    ∃ out,
      aspis_prover.aspis_core.field.M31.half x = ok out ∧
      runtimeCanonicalM31 out ∧
      ((out.val : Nat) : ExactM31) + (out.val : ExactM31) =
        (x.val : ExactM31) := by
  rcases AspisAeneasHalf.extracted_m31_half_corresponds x hx with
    ⟨out, hcall, _hraw, hcanonical, hhalf⟩
  refine ⟨out, ?_, hcanonical, ?_⟩
  · rw [runtime_m31_half_call_eq]
    exact hcall
  · have htwo : (2 : ExactM31) ≠ 0 := by decide
    rw [← mul_two]
    exact (eq_div_iff htwo).1 hhalf

theorem runtime_cm31_half_corresponds
    (x : RuntimeCM31) (hx : runtimeCanonicalCM31 x) :
    ∃ out,
      aspis_prover.aspis_core.field.CM31.half x = ok out ∧
      runtimeCanonicalCM31 out ∧
      runtimeCM31View out + runtimeCM31View out = runtimeCM31View x := by
  rcases runtime_m31_half_corresponds x.a hx.1 with
    ⟨oa, hcallA, hcanA, hdoubleA⟩
  rcases runtime_m31_half_corresponds x.b hx.2 with
    ⟨ob, hcallB, hcanB, hdoubleB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.CM31.half, hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · exact hdoubleA
    · exact hdoubleB

theorem runtime_qm31_half_corresponds
    (x : RuntimeQM31) (hx : runtimeCanonicalQM31 x) :
    ∃ out,
      aspis_prover.aspis_core.field.QM31.half x = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out = runtimeQM31View x / 2 := by
  rcases runtime_cm31_half_corresponds x.c0 hx.1 with
    ⟨o0, hcall0, hcan0, hdouble0⟩
  rcases runtime_cm31_half_corresponds x.c1 hx.2 with
    ⟨o1, hcall1, hcan1, hdouble1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.QM31.half, hcall0, hcall1]
  · have hdouble :
        runtimeQM31View ⟨o0, o1⟩ + runtimeQM31View ⟨o0, o1⟩ =
          runtimeQM31View x := by
      apply QuadraticAlgebra.ext
      · exact hdouble0
      · exact hdouble1
    have htwo : (2 : ExactQM31) ≠ 0 := by
      intro h
      have hre := congrArg (fun z : ExactQM31 => z.re.re) h
      change (2 : ExactM31) = 0 at hre
      exact (by decide : (2 : ExactM31) ≠ 0) hre
    apply (eq_div_iff htwo).2
    simpa [mul_two] using hdouble

theorem runtime_m31_add_mul_call_eq (x y : RuntimeM31) :
    aspis_prover.aspis_core.field.M31.add x y =
      AspisCoreCM31Multiplicative.field.M31.add x y := by
  simp [aspis_prover.aspis_core.field.M31.add,
    aspis_prover.aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.M31.add,
    AspisCoreCM31Multiplicative.field.P, Std.lift]

theorem runtime_m31_sub_mul_call_eq (x y : RuntimeM31) :
    aspis_prover.aspis_core.field.M31.sub x y =
      AspisCoreCM31Multiplicative.field.M31.sub x y := by
  simp [aspis_prover.aspis_core.field.M31.sub,
    aspis_prover.aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.M31.sub,
    AspisCoreCM31Multiplicative.field.P, Std.lift]

theorem runtime_reduce_u64_mul_call_eq (x : Std.U64) :
    aspis_prover.aspis_core.field.reduce_u64 x =
      AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  simp [aspis_prover.aspis_core.field.reduce_u64,
    aspis_prover.aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.reduce_u64,
    AspisCoreCM31Multiplicative.field.P, Std.lift]

theorem runtime_m31_mul_mul_call_eq (x y : RuntimeM31) :
    aspis_prover.aspis_core.field.M31.mul x y =
      AspisCoreCM31Multiplicative.field.M31.mul x y := by
  simp [aspis_prover.aspis_core.field.M31.mul,
    AspisCoreCM31Multiplicative.field.M31.mul,
    runtime_reduce_u64_mul_call_eq, Std.lift]

theorem runtime_m31_add_corresponds
    (x y : RuntimeM31)
    (hx : runtimeCanonicalM31 x) (hy : runtimeCanonicalM31 y) :
    ∃ out,
      aspis_prover.aspis_core.field.M31.add x y = ok out ∧
      runtimeCanonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) + (y.val : ExactM31) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x y hx hy with ⟨out, hcall, hcanonical, hview⟩
  refine ⟨out, ?_, hcanonical, hview⟩
  rw [runtime_m31_add_mul_call_eq]
  exact hcall

theorem runtime_m31_sub_corresponds
    (x y : RuntimeM31)
    (hx : runtimeCanonicalM31 x) (hy : runtimeCanonicalM31 y) :
    ∃ out,
      aspis_prover.aspis_core.field.M31.sub x y = ok out ∧
      runtimeCanonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) - (y.val : ExactM31) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      x y hx hy with ⟨out, hcall, hcanonical, hview⟩
  refine ⟨out, ?_, hcanonical, hview⟩
  rw [runtime_m31_sub_mul_call_eq]
  exact hcall

theorem runtime_cm31_add_corresponds
    (x y : RuntimeCM31)
    (hx : runtimeCanonicalCM31 x) (hy : runtimeCanonicalCM31 y) :
    ∃ out,
      aspis_prover.aspis_core.field.CM31.add x y = ok out ∧
      runtimeCanonicalCM31 out ∧
      runtimeCM31View out = runtimeCM31View x + runtimeCM31View y := by
  rcases runtime_m31_add_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hviewA⟩
  rcases runtime_m31_add_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hviewB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.CM31.add, hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · exact hviewA
    · exact hviewB

theorem runtime_cm31_sub_corresponds
    (x y : RuntimeCM31)
    (hx : runtimeCanonicalCM31 x) (hy : runtimeCanonicalCM31 y) :
    ∃ out,
      aspis_prover.aspis_core.field.CM31.sub x y = ok out ∧
      runtimeCanonicalCM31 out ∧
      runtimeCM31View out = runtimeCM31View x - runtimeCM31View y := by
  rcases runtime_m31_sub_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hviewA⟩
  rcases runtime_m31_sub_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hviewB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.CM31.sub, hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · exact hviewA
    · exact hviewB

theorem runtime_qm31_add_corresponds
    (x y : RuntimeQM31)
    (hx : runtimeCanonicalQM31 x) (hy : runtimeCanonicalQM31 y) :
    ∃ out,
      aspis_prover.aspis_core.field.QM31.add x y = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out = runtimeQM31View x + runtimeQM31View y := by
  rcases runtime_cm31_add_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨o0, hcall0, hcan0, hview0⟩
  rcases runtime_cm31_add_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨o1, hcall1, hcan1, hview1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.QM31.add, hcall0, hcall1]
  · apply QuadraticAlgebra.ext
    · exact hview0
    · exact hview1

theorem runtime_qm31_sub_corresponds
    (x y : RuntimeQM31)
    (hx : runtimeCanonicalQM31 x) (hy : runtimeCanonicalQM31 y) :
    ∃ out,
      aspis_prover.aspis_core.field.QM31.sub x y = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out = runtimeQM31View x - runtimeQM31View y := by
  rcases runtime_cm31_sub_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨o0, hcall0, hcan0, hview0⟩
  rcases runtime_cm31_sub_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨o1, hcall1, hcan1, hview1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.QM31.sub, hcall0, hcall1]
  · apply QuadraticAlgebra.ext
    · exact hview0
    · exact hview1

theorem runtime_wrapping_P_sub_val
    (x : RuntimeM31) (hx : runtimeCanonicalM31 x) :
    (Std.U32.wrapping_sub aspis_prover.aspis_core.field.P x).val =
      2147483647 - x.val := by
  rw [Std.U32.wrapping_sub_val_eq]
  simp only [aspis_prover.aspis_core.field.P, UScalar.ofNatCore_val_eq]
  have hsize : UScalar.size UScalarTy.U32 = 4294967296 := by
    rw [AspisAeneasCM31Multiplicative.u32_size_eq]
    norm_num [AspisAeneasCM31Multiplicative.u32Cardinality]
  rw [hsize]
  have hx' : x.val < 2147483647 := hx
  have hrewrite :
      2147483647 + (4294967296 - x.val) =
        (2147483647 - x.val) + 4294967296 := by
    omega
  rw [hrewrite, Nat.add_mod_right]
  apply Nat.mod_eq_of_lt
  omega

theorem runtime_m31_neg_corresponds
    (x : RuntimeM31) (hx : runtimeCanonicalM31 x) :
    ∃ out,
      aspis_prover.aspis_core.field.M31.neg x = ok out ∧
      runtimeCanonicalM31 out ∧
      runtimeM31View out = -runtimeM31View x := by
  by_cases hzero : x.val = 0
  · have hx0 : x = 0#u32 := UScalar.eq_of_val_eq hzero
    refine ⟨0#u32, ?_, ?_, ?_⟩
    · simp [aspis_prover.aspis_core.field.M31.neg, hx0]
    · norm_num [runtimeCanonicalM31,
        AspisAeneasCM31Multiplicative.CanonicalRawM31,
        AspisAeneasCM31Multiplicative.m31Modulus]
    · simp [runtimeM31View, hx0]
  · let out := Std.U32.wrapping_sub aspis_prover.aspis_core.field.P x
    have hout : out.val = AspisV5M31RawSubNeg.rawM31Neg x.val := by
      rw [runtime_wrapping_P_sub_val x hx]
      simp [AspisV5M31RawSubNeg.rawM31Neg, hzero]
    refine ⟨out, ?_, ?_, ?_⟩
    · simp [aspis_prover.aspis_core.field.M31.neg, hzero,
        out, Std.lift]
    · rw [runtimeCanonicalM31, hout]
      exact AspisV5M31RawSubNeg.rawM31Neg_canonical hx
    · apply QuadraticAlgebra.ext
      · apply QuadraticAlgebra.ext
        · change ((out.val : Nat) : ExactM31) = -((x.val : Nat) : ExactM31)
          rw [hout]
          exact AspisV5M31RawSubNeg.residue_rawM31Neg hx
        · simp [runtimeM31View]
      · simp [runtimeM31View]

theorem runtime_m31_mul_corresponds
    (x y : RuntimeM31)
    (hx : runtimeCanonicalM31 x) (hy : runtimeCanonicalM31 y) :
    ∃ out,
      aspis_prover.aspis_core.field.M31.mul x y = ok out ∧
      runtimeCanonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) * (y.val : ExactM31) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      x y hx hy with ⟨out, hcall, hcanonical, hview⟩
  refine ⟨out, ?_, hcanonical, hview⟩
  rw [runtime_m31_mul_mul_call_eq]
  exact hcall

theorem runtime_cm31_mul_corresponds
    (x y : RuntimeCM31)
    (hx : runtimeCanonicalCM31 x) (hy : runtimeCanonicalCM31 y) :
    ∃ out,
      aspis_prover.aspis_core.field.CM31.mul x y = ok out ∧
      runtimeCanonicalCM31 out ∧
      runtimeCM31View out = runtimeCM31View x * runtimeCM31View y := by
  rcases runtime_m31_mul_corresponds x.a y.a hx.1 hy.1 with
    ⟨m0, hm0, hcanM0, hviewM0⟩
  rcases runtime_m31_mul_corresponds x.b y.b hx.2 hy.2 with
    ⟨m1, hm1, hcanM1, hviewM1⟩
  rcases runtime_m31_add_corresponds x.a x.b hx.1 hx.2 with
    ⟨xsum, hxsum, hcanXsum, hviewXsum⟩
  rcases runtime_m31_add_corresponds y.a y.b hy.1 hy.2 with
    ⟨ysum, hysum, hcanYsum, hviewYsum⟩
  rcases runtime_m31_mul_corresponds xsum ysum hcanXsum hcanYsum with
    ⟨m2, hm2, hcanM2, hviewM2⟩
  rcases runtime_m31_sub_corresponds m0 m1 hcanM0 hcanM1 with
    ⟨real, hreal, hcanReal, hviewReal⟩
  rcases runtime_m31_sub_corresponds m2 m0 hcanM2 hcanM0 with
    ⟨imagPartial, himagPartial, hcanImagPartial, hviewImagPartial⟩
  rcases runtime_m31_sub_corresponds
      imagPartial m1 hcanImagPartial hcanM1 with
    ⟨imag, himag, hcanImag, hviewImag⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hcanReal, hcanImag⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.CM31.mul,
      hm0, hm1, hxsum, hysum, hm2, hreal, himagPartial, himag]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) =
        (runtimeCM31View x * runtimeCM31View y).re
      rw [hviewReal, hviewM0, hviewM1]
      simp [runtimeCM31View]
      ring_nf
    · change ((imag.val : Nat) : ExactM31) =
        (runtimeCM31View x * runtimeCM31View y).im
      rw [hviewImag, hviewImagPartial, hviewM2,
        hviewXsum, hviewYsum, hviewM0, hviewM1]
      simp [runtimeCM31View]
      ring

theorem runtime_mul_by_r_corresponds
    (x : RuntimeCM31) (hx : runtimeCanonicalCM31 x) :
    ∃ out,
      aspis_prover.aspis_core.field.mul_by_r x = ok out ∧
      runtimeCanonicalCM31 out ∧
      runtimeCM31View out =
        runtimeCM31View x * AspisAeneasQM31Mul.qm31R := by
  rcases runtime_m31_add_corresponds x.a x.a hx.1 hx.1 with
    ⟨twoA, htwoA, hcanTwoA, hviewTwoA⟩
  rcases runtime_m31_sub_corresponds twoA x.b hcanTwoA hx.2 with
    ⟨real, hreal, hcanReal, hviewReal⟩
  rcases runtime_m31_add_corresponds x.b x.b hx.2 hx.2 with
    ⟨twoB, htwoB, hcanTwoB, hviewTwoB⟩
  rcases runtime_m31_add_corresponds x.a twoB hx.1 hcanTwoB with
    ⟨imag, himag, hcanImag, hviewImag⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hcanReal, hcanImag⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.mul_by_r,
      aspis_prover.aspis_core.field.M31.double,
      htwoA, hreal, htwoB, himag]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) =
        (runtimeCM31View x * AspisAeneasQM31Mul.qm31R).re
      rw [hviewReal, hviewTwoA]
      simp [runtimeCM31View, AspisAeneasQM31Mul.qm31R]
      ring
    · change ((imag.val : Nat) : ExactM31) =
        (runtimeCM31View x * AspisAeneasQM31Mul.qm31R).im
      rw [hviewImag, hviewTwoB]
      simp [runtimeCM31View, AspisAeneasQM31Mul.qm31R]
      ring

theorem runtime_qm31_mul_corresponds
    (x y : RuntimeQM31)
    (hx : runtimeCanonicalQM31 x) (hy : runtimeCanonicalQM31 y) :
    ∃ out,
      aspis_prover.aspis_core.field.QM31.mul x y = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out = runtimeQM31View x * runtimeQM31View y := by
  rcases runtime_cm31_mul_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨m0, hm0, hcanM0, hviewM0⟩
  rcases runtime_cm31_mul_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨m1, hm1, hcanM1, hviewM1⟩
  rcases runtime_cm31_add_corresponds x.c0 x.c1 hx.1 hx.2 with
    ⟨xsum, hxsum, hcanXsum, hviewXsum⟩
  rcases runtime_cm31_add_corresponds y.c0 y.c1 hy.1 hy.2 with
    ⟨ysum, hysum, hcanYsum, hviewYsum⟩
  rcases runtime_cm31_mul_corresponds xsum ysum hcanXsum hcanYsum with
    ⟨m2, hm2, hcanM2, hviewM2⟩
  rcases runtime_mul_by_r_corresponds m1 hcanM1 with
    ⟨rM1, hrM1, hcanRM1, hviewRM1⟩
  rcases runtime_cm31_add_corresponds m0 rM1 hcanM0 hcanRM1 with
    ⟨low, hlow, hcanLow, hviewLow⟩
  rcases runtime_cm31_sub_corresponds m2 m0 hcanM2 hcanM0 with
    ⟨highPartial, hhighPartial, hcanHighPartial, hviewHighPartial⟩
  rcases runtime_cm31_sub_corresponds
      highPartial m1 hcanHighPartial hcanM1 with
    ⟨high, hhigh, hcanHigh, hviewHigh⟩
  have hR : AspisAeneasQM31Mul.qm31R =
      AspisV5ComponentCQM31TowerExact.qm31R := by rfl
  rw [hR] at hviewRM1
  refine ⟨⟨low, high⟩, ?_, ⟨hcanLow, hcanHigh⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.QM31.mul,
      hm0, hm1, hxsum, hysum, hm2, hrM1, hlow, hhighPartial, hhigh]
  · apply QuadraticAlgebra.ext
    · change runtimeCM31View low =
        (runtimeQM31View x * runtimeQM31View y).re
      rw [hviewLow, hviewM0, hviewRM1, hviewM1]
      simp [runtimeQM31View]
      ring
    · change runtimeCM31View high =
        (runtimeQM31View x * runtimeQM31View y).im
      rw [hviewHigh, hviewHighPartial, hviewM2,
        hviewXsum, hviewYsum, hviewM0, hviewM1]
      simp [runtimeQM31View]
      ring

theorem runtime_cm31_mul_m31_corresponds
    (x : RuntimeCM31) (r : RuntimeM31)
    (hx : runtimeCanonicalCM31 x) (hr : runtimeCanonicalM31 r) :
    ∃ out,
      aspis_prover.aspis_core.field.CM31.mul_m31 x r = ok out ∧
      runtimeCanonicalCM31 out ∧
      runtimeCM31View out = runtimeCM31View x * runtimeM31CMView r := by
  rcases runtime_m31_mul_corresponds x.a r hx.1 hr with
    ⟨oa, hcallA, hcanA, hviewA⟩
  rcases runtime_m31_mul_corresponds x.b r hx.2 hr with
    ⟨ob, hcallB, hcanB, hviewB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.CM31.mul_m31, hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · simpa [runtimeCM31View, runtimeM31CMView] using hviewA
    · simpa [runtimeCM31View, runtimeM31CMView] using hviewB

theorem runtime_qm31_mul_m31_corresponds
    (x : RuntimeQM31) (r : RuntimeM31)
    (hx : runtimeCanonicalQM31 x) (hr : runtimeCanonicalM31 r) :
    ∃ out,
      aspis_prover.aspis_core.field.QM31.mul_m31 x r = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out = runtimeQM31View x * runtimeM31View r := by
  rcases runtime_cm31_mul_m31_corresponds x.c0 r hx.1 hr with
    ⟨o0, hcall0, hcan0, hview0⟩
  rcases runtime_cm31_mul_m31_corresponds x.c1 r hx.2 hr with
    ⟨o1, hcall1, hcan1, hview1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [aspis_prover.aspis_core.field.QM31.mul_m31, hcall0, hcall1]
  · apply QuadraticAlgebra.ext
    · change runtimeCM31View o0 =
        (runtimeQM31View x * runtimeM31View r).re
      rw [hview0]
      simp [runtimeQM31View, runtimeM31View, runtimeM31CMView]
    · change runtimeCM31View o1 =
        (runtimeQM31View x * runtimeM31View r).im
      rw [hview1]
      simp [runtimeQM31View, runtimeM31View, runtimeM31CMView]

/-- All five field operations used by the extracted line fold are discharged
against independently authenticated source extractions of the shared field
implementation. -/
def runtimeFoldPrimitiveLaws : RuntimeFoldPrimitiveLaws ExactQM31 where
  canonicalM31 := runtimeCanonicalM31
  canonicalQM31 := runtimeCanonicalQM31
  m31View := runtimeM31View
  qm31View := runtimeQM31View
  add := runtime_qm31_add_corresponds
  sub := runtime_qm31_sub_corresponds
  mul := runtime_qm31_mul_corresponds
  half := runtime_qm31_half_corresponds
  mulM31 := runtime_qm31_mul_m31_corresponds

/-- The circle fold's additional base-field negation is discharged by the
same source-authentic additive extraction. -/
def runtimeCirclePrimitiveLaws : RuntimeCirclePrimitiveLaws ExactQM31 where
  toRuntimeFoldPrimitiveLaws := runtimeFoldPrimitiveLaws
  negM31 := runtime_m31_neg_corresponds

/-- Unconditional primitive-semantics capstone for the source-authentic line
fold.  Only canonical input representations and the caller's genuine
`alphaSquared = alpha^2` relation remain as value-level preconditions. -/
theorem extracted_prepared_line_fold_exact
    (v0 v1 v2 v3 alpha alphaSquared : RuntimeQM31)
    (inv0 inv1 inv2 : RuntimeM31)
    (hv0 : runtimeCanonicalQM31 v0)
    (hv1 : runtimeCanonicalQM31 v1)
    (hv2 : runtimeCanonicalQM31 v2)
    (hv3 : runtimeCanonicalQM31 v3)
    (halpha : runtimeCanonicalQM31 alpha)
    (halphaSquared : runtimeCanonicalQM31 alphaSquared)
    (hinv0 : runtimeCanonicalM31 inv0)
    (hinv1 : runtimeCanonicalM31 inv1)
    (hinv2 : runtimeCanonicalM31 inv2)
    (halphaSquaredView :
      runtimeQM31View alphaSquared = runtimeQM31View alpha ^ 2) :
    ∃ out,
      aspis_prover.aspis_core.circle_fri.normalized_line_arity4_prepared_with_square
          (Array.make 4#usize [v0, v1, v2, v3]) alpha alphaSquared
          (Array.make 3#usize [inv0, inv1, inv2]) = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out =
        AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
          (runtimeQM31View alpha)
          (runtimeM31View inv0) (runtimeM31View inv1) (runtimeM31View inv2)
          (orderedFour (runtimeQM31View v0) (runtimeQM31View v1)
            (runtimeQM31View v2) (runtimeQM31View v3)) := by
  exact extracted_prepared_line_fold_eq_maintained
    runtimeFoldPrimitiveLaws v0 v1 v2 v3 alpha alphaSquared
    inv0 inv1 inv2 hv0 hv1 hv2 hv3 halpha halphaSquared
    hinv0 hinv1 hinv2 halphaSquaredView

/-- Unconditional primitive-semantics capstone for the source-authentic
circle-to-line fold, including the deployed `-inv_2y` convention. -/
theorem extracted_prepared_circle_fold_exact
    (v0 v1 v2 v3 alpha alphaSquared : RuntimeQM31)
    (inv2x inv2y : RuntimeM31)
    (hv0 : runtimeCanonicalQM31 v0)
    (hv1 : runtimeCanonicalQM31 v1)
    (hv2 : runtimeCanonicalQM31 v2)
    (hv3 : runtimeCanonicalQM31 v3)
    (halpha : runtimeCanonicalQM31 alpha)
    (halphaSquared : runtimeCanonicalQM31 alphaSquared)
    (hinv2x : runtimeCanonicalM31 inv2x)
    (hinv2y : runtimeCanonicalM31 inv2y)
    (halphaSquaredView :
      runtimeQM31View alphaSquared = runtimeQM31View alpha ^ 2) :
    ∃ out,
      aspis_prover.aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_with_square
          (Array.make 4#usize [v0, v1, v2, v3]) alpha alphaSquared
          inv2x inv2y = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out =
        AspisV5ComponentCConcreteFoldLinearity.circleFoldValue
          (runtimeQM31View alpha) (runtimeM31View inv2x)
          (runtimeM31View inv2y)
          (orderedFour (runtimeQM31View v0) (runtimeQM31View v1)
            (runtimeQM31View v2) (runtimeQM31View v3)) := by
  exact extracted_prepared_circle_fold_eq_maintained
    runtimeCirclePrimitiveLaws v0 v1 v2 v3 alpha alphaSquared
    inv2x inv2y hv0 hv1 hv2 hv3 halpha halphaSquared
    hinv2x hinv2y halphaSquaredView

end aspis_prover.ComponentCRuntimeFoldPrimitiveInstantiation
