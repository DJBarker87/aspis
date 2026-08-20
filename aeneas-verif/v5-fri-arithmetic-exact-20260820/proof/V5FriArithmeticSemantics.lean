import FriArithmetic.Funs
import QM31MulProof
import HalfProof
import AspisFormal.V5ComponentCConcreteFoldLinearity
import AspisFormal.V5ComponentCQM31TowerExact

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 5000

/-!
# Exact semantics of the production V5 FRI arithmetic helpers

This file starts from the focused Charon/Aeneas extraction of the unchanged
`aspis-core` functions used by the deployed FRI consumer.  It does not assume
the result of a fold.  Instead it reuses the independently proved raw M31 and
QM31 arithmetic facts and proves the value represented by every successful
generated call.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriArithmeticSemantics

namespace Fresh
open V5FriArithmeticExact

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev QM31 := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier

end Fresh

abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExactCM31 := AspisV5ComponentCQM31TowerExact.CM31Exact
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def canonicalM31 (x : Fresh.M31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 x.val

def canonicalCM31 (x : Fresh.CM31) : Prop :=
  canonicalM31 x.a ∧ canonicalM31 x.b

def canonicalQM31 (x : Fresh.QM31) : Prop :=
  canonicalCM31 x.c0 ∧ canonicalCM31 x.c1

def m31View (x : Fresh.M31) : ExactQM31 :=
  ⟨⟨(x.val : ExactM31), 0⟩, 0⟩

def m31CMView (x : Fresh.M31) : ExactCM31 :=
  ⟨(x.val : ExactM31), 0⟩

def cm31View (x : Fresh.CM31) : ExactCM31 :=
  ⟨(x.a.val : ExactM31), (x.b.val : ExactM31)⟩

def qm31View (x : Fresh.QM31) : ExactQM31 :=
  ⟨cm31View x.c0, cm31View x.c1⟩

private theorem fresh_P_eq_multiplicative :
    V5FriArithmeticExact.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5FriArithmeticExact.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem fresh_m31_add_call_eq_multiplicative (x y : Fresh.M31) :
    V5FriArithmeticExact.field.M31.add x y =
      AspisCoreCM31Multiplicative.field.M31.add x y := by
  unfold V5FriArithmeticExact.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [fresh_P_eq_multiplicative]

private theorem fresh_m31_sub_call_eq_multiplicative (x y : Fresh.M31) :
    V5FriArithmeticExact.field.M31.sub x y =
      AspisCoreCM31Multiplicative.field.M31.sub x y := by
  unfold V5FriArithmeticExact.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [fresh_P_eq_multiplicative]

private theorem fresh_reduce_u64_call_eq_multiplicative (x : Std.U64) :
    V5FriArithmeticExact.field.reduce_u64 x =
      AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  unfold V5FriArithmeticExact.field.reduce_u64
    AspisCoreCM31Multiplicative.field.reduce_u64
  rw [fresh_P_eq_multiplicative]

private theorem fresh_m31_mul_call_eq_multiplicative (x y : Fresh.M31) :
    V5FriArithmeticExact.field.M31.mul x y =
      AspisCoreCM31Multiplicative.field.M31.mul x y := by
  unfold V5FriArithmeticExact.field.M31.mul
    AspisCoreCM31Multiplicative.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [fresh_reduce_u64_call_eq_multiplicative]

private theorem fresh_P_eq_half :
    V5FriArithmeticExact.field.P = AspisCoreHalf.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5FriArithmeticExact.field.P AspisCoreHalf.field.P
  rfl

private theorem fresh_m31_half_call_eq_half (x : Fresh.M31) :
    V5FriArithmeticExact.field.M31.half x =
      AspisCoreHalf.field.M31.half x := by
  unfold V5FriArithmeticExact.field.M31.half
    AspisCoreHalf.field.M31.half
  simp only [Std.lift, bind_tc_ok]
  rw [fresh_P_eq_half, halfShiftCountOne_exact]

theorem m31_add_corresponds
    (x y : Fresh.M31) (hx : canonicalM31 x) (hy : canonicalM31 y) :
    ∃ out,
      V5FriArithmeticExact.field.M31.add x y = ok out ∧
      canonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) + (y.val : ExactM31) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x y hx hy with
    ⟨out, hcall, hcanonical, hview⟩
  exact ⟨out, fresh_m31_add_call_eq_multiplicative x y |>.trans hcall,
    hcanonical, hview⟩

theorem m31_sub_corresponds
    (x y : Fresh.M31) (hx : canonicalM31 x) (hy : canonicalM31 y) :
    ∃ out,
      V5FriArithmeticExact.field.M31.sub x y = ok out ∧
      canonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) - (y.val : ExactM31) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      x y hx hy with
    ⟨out, hcall, hcanonical, hview⟩
  exact ⟨out, fresh_m31_sub_call_eq_multiplicative x y |>.trans hcall,
    hcanonical, hview⟩

theorem m31_mul_corresponds
    (x y : Fresh.M31) (hx : canonicalM31 x) (hy : canonicalM31 y) :
    ∃ out,
      V5FriArithmeticExact.field.M31.mul x y = ok out ∧
      canonicalM31 out ∧
      ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) * (y.val : ExactM31) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      x y hx hy with
    ⟨out, hcall, hcanonical, hview⟩
  exact ⟨out, fresh_m31_mul_call_eq_multiplicative x y |>.trans hcall,
    hcanonical, hview⟩

theorem m31_half_corresponds
    (x : Fresh.M31) (hx : canonicalM31 x) :
    ∃ out,
      V5FriArithmeticExact.field.M31.half x = ok out ∧
      canonicalM31 out ∧
      ((out.val : Nat) : ExactM31) = (x.val : ExactM31) / 2 := by
  rcases AspisAeneasHalf.extracted_m31_half_corresponds x hx with
    ⟨out, hcall, _hraw, hcanonical, hview⟩
  exact ⟨out, fresh_m31_half_call_eq_half x |>.trans hcall,
    hcanonical, hview⟩

theorem m31_neg_corresponds
    (x : Fresh.M31) (hx : canonicalM31 x) :
    ∃ out,
      V5FriArithmeticExact.field.M31.neg x = ok out ∧
      canonicalM31 out ∧
      ((out.val : Nat) : ExactM31) = -(x.val : ExactM31) := by
  by_cases hzero : x = 0#u32
  · subst x
    refine ⟨0#u32, ?_, ?_, ?_⟩
    · simp [V5FriArithmeticExact.field.M31.neg]
    · norm_num [canonicalM31,
        AspisAeneasCM31Multiplicative.CanonicalRawM31,
        AspisAeneasCM31Multiplicative.m31Modulus]
    · simp
  · let out := Std.U32.wrapping_sub V5FriArithmeticExact.field.P x
    have hxval : x.val < 2147483647 := hx
    have houtval : out.val = 2147483647 - x.val := by
      rw [Std.U32.wrapping_sub_val_eq]
      simp only [out, V5FriArithmeticExact.field.P,
        UScalar.ofNatCore_val_eq]
      have hsize : UScalar.size UScalarTy.U32 = 4294967296 := by
        rw [AspisAeneasCM31Multiplicative.u32_size_eq]
        norm_num [AspisAeneasCM31Multiplicative.u32Cardinality]
      rw [hsize]
      have hrewrite :
          2147483647 + (4294967296 - x.val) =
            (2147483647 - x.val) + 4294967296 := by omega
      rw [hrewrite, Nat.add_mod_right]
      apply Nat.mod_eq_of_lt
      omega
    refine ⟨out, ?_, ?_, ?_⟩
    · simp [V5FriArithmeticExact.field.M31.neg, hzero, out, Std.lift]
    · change out.val < 2147483647
      rw [houtval]
      have hxpos : 0 < x.val := by
        apply Nat.pos_of_ne_zero
        intro hxzero
        apply hzero
        exact UScalar.eq_of_val_eq hxzero
      omega
    · change ((out.val : Nat) : ExactM31) = -((x.val : Nat) : ExactM31)
      rw [houtval]
      calc
        (((2147483647 - x.val : Nat) : ExactM31)) =
            ((2147483647 : Nat) : ExactM31) -
              ((x.val : Nat) : ExactM31) := by
                rw [Nat.cast_sub (by omega : x.val ≤ 2147483647)]
        _ = 0 - ((x.val : Nat) : ExactM31) := by
          change ((2147483647 : Nat) : ZMod 2147483647) - _ = _
          rw [ZMod.natCast_self]
        _ = -((x.val : Nat) : ExactM31) := zero_sub _

theorem cm31_add_corresponds
    (x y : Fresh.CM31) (hx : canonicalCM31 x) (hy : canonicalCM31 y) :
    ∃ out,
      V5FriArithmeticExact.field.CM31.add x y = ok out ∧
      canonicalCM31 out ∧ cm31View out = cm31View x + cm31View y := by
  rcases m31_add_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hviewA⟩
  rcases m31_add_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hviewB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [V5FriArithmeticExact.field.CM31.add, hcallA, hcallB]
  · apply QuadraticAlgebra.ext <;> assumption

theorem cm31_sub_corresponds
    (x y : Fresh.CM31) (hx : canonicalCM31 x) (hy : canonicalCM31 y) :
    ∃ out,
      V5FriArithmeticExact.field.CM31.sub x y = ok out ∧
      canonicalCM31 out ∧ cm31View out = cm31View x - cm31View y := by
  rcases m31_sub_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hviewA⟩
  rcases m31_sub_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hviewB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [V5FriArithmeticExact.field.CM31.sub, hcallA, hcallB]
  · apply QuadraticAlgebra.ext <;> assumption

theorem cm31_half_corresponds
    (x : Fresh.CM31) (hx : canonicalCM31 x) :
    ∃ out,
      V5FriArithmeticExact.field.CM31.half x = ok out ∧
      canonicalCM31 out ∧
        cm31View out = cm31View x / (2 : ExactCM31) := by
  rcases m31_half_corresponds x.a hx.1 with ⟨oa, hcallA, hcanA, hviewA⟩
  rcases m31_half_corresponds x.b hx.2 with ⟨ob, hcallB, hcanB, hviewB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [V5FriArithmeticExact.field.CM31.half, hcallA, hcallB]
  · have hdouble :
        cm31View ⟨oa, ob⟩ + cm31View ⟨oa, ob⟩ = cm31View x := by
      apply QuadraticAlgebra.ext
      · change ((oa.val : Nat) : ExactM31) + (oa.val : ExactM31) =
          (x.a.val : ExactM31)
        rw [hviewA]
        field_simp
      · change ((ob.val : Nat) : ExactM31) + (ob.val : ExactM31) =
          (x.b.val : ExactM31)
        rw [hviewB]
        field_simp
    have htwo : (2 : ExactCM31) ≠ 0 := by
      intro h
      have hre := congrArg (fun z : ExactCM31 => z.re) h
      change (2 : ExactM31) = 0 at hre
      exact (by decide : (2 : ExactM31) ≠ 0) hre
    apply (eq_div_iff htwo).2
    simpa [mul_two] using hdouble

theorem cm31_mul_m31_corresponds
    (x : Fresh.CM31) (r : Fresh.M31)
    (hx : canonicalCM31 x) (hr : canonicalM31 r) :
    ∃ out,
      V5FriArithmeticExact.field.CM31.mul_m31 x r = ok out ∧
      canonicalCM31 out ∧ cm31View out = cm31View x * m31CMView r := by
  rcases m31_mul_corresponds x.a r hx.1 hr with
    ⟨oa, hcallA, hcanA, hviewA⟩
  rcases m31_mul_corresponds x.b r hx.2 hr with
    ⟨ob, hcallB, hcanB, hviewB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [V5FriArithmeticExact.field.CM31.mul_m31, hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · simpa [cm31View, m31CMView] using hviewA
    · simpa [cm31View, m31CMView] using hviewB

theorem qm31_add_corresponds
    (x y : Fresh.QM31) (hx : canonicalQM31 x) (hy : canonicalQM31 y) :
    ∃ out,
      V5FriArithmeticExact.field.QM31.add x y = ok out ∧
      canonicalQM31 out ∧ qm31View out = qm31View x + qm31View y := by
  rcases cm31_add_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨o0, hcall0, hcan0, hview0⟩
  rcases cm31_add_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨o1, hcall1, hcan1, hview1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [V5FriArithmeticExact.field.QM31.add, hcall0, hcall1]
  · apply QuadraticAlgebra.ext <;> assumption

theorem qm31_sub_corresponds
    (x y : Fresh.QM31) (hx : canonicalQM31 x) (hy : canonicalQM31 y) :
    ∃ out,
      V5FriArithmeticExact.field.QM31.sub x y = ok out ∧
      canonicalQM31 out ∧ qm31View out = qm31View x - qm31View y := by
  rcases cm31_sub_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨o0, hcall0, hcan0, hview0⟩
  rcases cm31_sub_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨o1, hcall1, hcan1, hview1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [V5FriArithmeticExact.field.QM31.sub, hcall0, hcall1]
  · apply QuadraticAlgebra.ext <;> assumption

theorem qm31_half_corresponds
    (x : Fresh.QM31) (hx : canonicalQM31 x) :
    ∃ out,
      V5FriArithmeticExact.field.QM31.half x = ok out ∧
      canonicalQM31 out ∧
        qm31View out = qm31View x / (2 : ExactQM31) := by
  rcases cm31_half_corresponds x.c0 hx.1 with
    ⟨o0, hcall0, hcan0, hview0⟩
  rcases cm31_half_corresponds x.c1 hx.2 with
    ⟨o1, hcall1, hcan1, hview1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [V5FriArithmeticExact.field.QM31.half, hcall0, hcall1]
  · have hdouble :
        qm31View ⟨o0, o1⟩ + qm31View ⟨o0, o1⟩ = qm31View x := by
      apply QuadraticAlgebra.ext
      · exact (eq_div_iff (by
          intro h
          have hre := congrArg (fun z : ExactCM31 => z.re) h
          change (2 : ExactM31) = 0 at hre
          exact (by decide : (2 : ExactM31) ≠ 0) hre)).1 hview0 |>
            (by simpa [mul_two] using ·)
      · exact (eq_div_iff (by
          intro h
          have hre := congrArg (fun z : ExactCM31 => z.re) h
          change (2 : ExactM31) = 0 at hre
          exact (by decide : (2 : ExactM31) ≠ 0) hre)).1 hview1 |>
            (by simpa [mul_two] using ·)
    have htwo : (2 : ExactQM31) ≠ 0 := by
      intro h
      have hre := congrArg (fun z : ExactQM31 => z.re.re) h
      change (2 : ExactM31) = 0 at hre
      exact (by decide : (2 : ExactM31) ≠ 0) hre
    apply (eq_div_iff htwo).2
    simpa [mul_two] using hdouble

theorem qm31_mul_m31_corresponds
    (x : Fresh.QM31) (r : Fresh.M31)
    (hx : canonicalQM31 x) (hr : canonicalM31 r) :
    ∃ out,
      V5FriArithmeticExact.field.QM31.mul_m31 x r = ok out ∧
      canonicalQM31 out ∧ qm31View out = qm31View x * m31View r := by
  rcases cm31_mul_m31_corresponds x.c0 r hx.1 hr with
    ⟨o0, hcall0, hcan0, hview0⟩
  rcases cm31_mul_m31_corresponds x.c1 r hx.2 hr with
    ⟨o1, hcall1, hcan1, hview1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [V5FriArithmeticExact.field.QM31.mul_m31, hcall0, hcall1]
  · apply QuadraticAlgebra.ext
    · simpa [qm31View, m31View, m31CMView] using hview0
    · simpa [qm31View, m31View, m31CMView] using hview1

end AspisV5FriArithmeticSemantics
