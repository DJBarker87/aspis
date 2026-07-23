import GoodMatricesCurrent.SourceExtractedField
import AspisFormal.V5M31RawSubNeg

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedTerminalField

open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCQM31RustFormulaSeam
open AspisV5M31RawMulReduction
open AspisV5M31RawSubNeg

abbrev LocalM31 := aspis_verifier.aspis_core.field.M31
abbrev LocalCM31 := aspis_verifier.aspis_core.field.CM31
abbrev LocalQM31 := aspis_verifier.aspis_core.field.QM31
abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExactCM31 := AspisV5ComponentCQM31TowerExact.CM31Exact
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def CanonicalLocalM31 (value : LocalM31) : Prop := value.val < P

def CanonicalLocalCM31 (value : LocalCM31) : Prop :=
  CanonicalLocalM31 value.a ∧ CanonicalLocalM31 value.b

def CanonicalLocalQM31 (value : LocalQM31) : Prop :=
  CanonicalLocalCM31 value.c0 ∧ CanonicalLocalCM31 value.c1

def cm31ToExact (value : LocalCM31) : ExactCM31 :=
  ⟨(value.a.val : ExactM31), (value.b.val : ExactM31)⟩

def qm31ToExact (value : LocalQM31) : ExactQM31 :=
  ⟨cm31ToExact value.c0, cm31ToExact value.c1⟩

private theorem canonical_eq_field_canonical (value : LocalM31) :
    CanonicalLocalM31 value =
      GoodMatricesCurrent.SourceExtractedField.CanonicalLocalM31 value := by
  rfl

theorem local_m31_add_corresponds (left right : LocalM31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : LocalM31,
      aspis_verifier.aspis_core.field.M31.add left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) + (right.val : ExactM31) := by
  simpa only [canonical_eq_field_canonical,
    GoodMatricesCurrent.SourceExtractedField.m31ToExact] using
    (GoodMatricesCurrent.SourceExtractedField.local_m31_add_exact_spec
      left right (by simpa [canonical_eq_field_canonical] using hleft)
        (by simpa [canonical_eq_field_canonical] using hright))

#exit

private theorem u32_wrapping_add_val_exact (left right : Std.U32)
    (hbound : left.val + right.val < UScalar.size .U32) :
    (Std.U32.wrapping_add left right).val = left.val + right.val := by
  rw [Std.U32.wrapping_add_val_eq, Nat.mod_eq_of_lt hbound]

private theorem u32_wrapping_sub_val_of_le (left right : Std.U32)
    (hle : right.val ≤ left.val) :
    (Std.U32.wrapping_sub left right).val = left.val - right.val := by
  rw [Std.U32.wrapping_sub_val_eq]
  have hrearrange :
      left.val + (UScalar.size .U32 - right.val) =
        (left.val - right.val) + UScalar.size .U32 := by
    have hleft := left.hSize
    have hright := right.hSize
    omega
  rw [hrearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by
    have hleft := left.hSize
    omega)

theorem root_m31_sub_corresponds (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.sub left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) - (right.val : ExactM31) := by
  let biased : Std.U32 := Std.U32.wrapping_add left 2147483647#u32
  let reduced : Std.U32 := Std.U32.wrapping_sub biased right
  have hbiasedBound : left.val + P < UScalar.size .U32 := by
    have h := canonicalRawM31_sub_add_lt_u32 hleft hright
    simpa [UScalar.size, Std.U32.size, Std.U32.numBits] using h
  have hbiased : biased.val = left.val + P := by
    unfold biased
    rw [u32_wrapping_add_val_exact]
    · norm_num [P]
    · simpa [P] using hbiasedBound
  have hnoUnderflow : right.val ≤ biased.val := by
    rw [hbiased]
    exact canonicalRawM31_sub_no_underflow hleft hright
  have hreduced : reduced.val = left.val + P - right.val := by
    unfold reduced
    rw [u32_wrapping_sub_val_of_le _ _ hnoUnderflow, hbiased]
  by_cases hhigh : P ≤ reduced.val
  · have hcondition : reduced >= 2147483647#u32 := by
      apply (UScalar.le_equiv _ _).2
      simpa [P] using hhigh
    let output := Std.U32.wrapping_sub reduced 2147483647#u32
    have hout : output.val = left.val + P - right.val - P := by
      unfold output
      rw [u32_wrapping_sub_val_of_le]
      · rw [hreduced]
        norm_num [P]
      · exact (UScalar.le_equiv _ _).1 hcondition
    refine ⟨output, ?_, ?_, ?_⟩
    · unfold _root_.aspis_core.field.M31.sub
      unfold AspisCoreAdditive.field.M31.sub
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [AspisCoreAdditive.field.P]
      rw [if_pos (by simpa [reduced, P] using hhigh)]
      rfl
    · change output.val < P
      rw [hout]
      exact (rawM31Sub_high_branch hleft hright (by simpa [hreduced] using hhigh)).2.2
    · calc
        (output.val : ExactM31) =
            (rawM31Sub left.val right.val : ExactM31) := by
              rw [(rawM31Sub_high_branch hleft hright
                (by simpa [hreduced] using hhigh)).1, hout]
        _ = (left.val : ExactM31) - (right.val : ExactM31) :=
          residue_rawM31Sub hleft hright
  · have hcondition : ¬ reduced >= 2147483647#u32 := by
      intro hge
      apply hhigh
      have := (UScalar.le_equiv _ _).1 hge
      simpa [P] using this
    refine ⟨reduced, ?_, ?_, ?_⟩
    · unfold _root_.aspis_core.field.M31.sub
      unfold AspisCoreAdditive.field.M31.sub
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [AspisCoreAdditive.field.P]
      rw [if_neg (by simpa [reduced, P] using hcondition)]
    · change reduced.val < P
      omega
    · rw [hreduced]
      have hlow : left.val + P - right.val < P := by omega
      calc
        ((left.val + P - right.val : Nat) : ExactM31) =
            (rawM31Sub left.val right.val : ExactM31) := by
              rw [(rawM31Sub_low_branch hlow).1]
        _ = (left.val : ExactM31) - (right.val : ExactM31) :=
          residue_rawM31Sub hleft hright

private theorem u64_cast_u32_val (value : Std.U32) :
    (UScalar.cast .U64 value : Std.U64).val = value.val := by
  simp

theorem root_m31_mul_corresponds (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.mul left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) * (right.val : ExactM31) := by
  let wideLeft : Std.U64 := UScalar.cast .U64 left
  let wideRight : Std.U64 := UScalar.cast .U64 right
  let product : Std.U64 := Std.U64.wrapping_mul wideLeft wideRight
  have hproductBound : left.val * right.val < 2 ^ 64 :=
    canonicalMul_lt_two_pow64 hleft hright
  have hproduct : product.val = left.val * right.val := by
    unfold product
    rw [Std.U64.wrapping_mul_val_eq, u64_cast_u32_val, u64_cast_u32_val]
    apply Nat.mod_eq_of_lt
    simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hproductBound
  obtain ⟨output, hcall, hout⟩ :=
    GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec product
  refine ⟨output, ?_, ?_, ?_⟩
  · unfold _root_.aspis_core.field.M31.mul
    unfold AuthenticFieldPow.field.M31.mul
    simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
    simp [wideLeft, wideRight, product, hcall]
  · change output.val < P
    rw [hout, hproduct]
    exact rawReduceU64_canonical _ hproductBound
  · rw [hout, hproduct]
    exact rawReduceU64_residue _ hproductBound |>.trans (by rw [Nat.cast_mul])

theorem root_m31_add_corresponds (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.add left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) + (right.val : ExactM31) := by
  simpa [aspis_verifier.aspis_core.field.M31.add] using
    local_m31_add_corresponds left right hleft hright

abbrev RootCM31 := _root_.aspis_core.field.CM31
abbrev RootQM31 := _root_.aspis_core.field.QM31

def CanonicalRootCM31 (value : RootCM31) : Prop :=
  CanonicalLocalM31 value.a ∧ CanonicalLocalM31 value.b

def CanonicalRootQM31 (value : RootQM31) : Prop :=
  CanonicalRootCM31 value.c0 ∧ CanonicalRootCM31 value.c1

def rootCM31ToExact (value : RootCM31) : ExactCM31 :=
  ⟨(value.a.val : ExactM31), (value.b.val : ExactM31)⟩

def rootQM31ToExact (value : RootQM31) : ExactQM31 :=
  ⟨rootCM31ToExact value.c0, rootCM31ToExact value.c1⟩

theorem root_cm31_add_corresponds (left right : RootCM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right) :
    ∃ output : RootCM31,
      _root_.aspis_core.field.CM31.add left right = .ok output ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact left + rootCM31ToExact right := by
  rcases root_m31_add_corresponds left.a right.a hleft.1 hright.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases root_m31_add_corresponds left.b right.b hleft.2 hright.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [_root_.aspis_core.field.CM31.add, hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem root_cm31_sub_corresponds (left right : RootCM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right) :
    ∃ output : RootCM31,
      _root_.aspis_core.field.CM31.sub left right = .ok output ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact left - rootCM31ToExact right := by
  rcases root_m31_sub_corresponds left.a right.a hleft.1 hright.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases root_m31_sub_corresponds left.b right.b hleft.2 hright.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [_root_.aspis_core.field.CM31.sub,
      AspisCoreAdditive.field.CM31.sub, hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem root_cm31_mul_corresponds (left right : RootCM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right) :
    ∃ output : RootCM31,
      _root_.aspis_core.field.CM31.mul left right = .ok output ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact left * rootCM31ToExact right := by
  rcases root_m31_mul_corresponds left.a right.a hleft.1 hright.1 with
    ⟨m0, hm0, hm0Can, hm0Exact⟩
  rcases root_m31_mul_corresponds left.b right.b hleft.2 hright.2 with
    ⟨m1, hm1, hm1Can, hm1Exact⟩
  rcases root_m31_add_corresponds left.a left.b hleft.1 hleft.2 with
    ⟨leftSum, hleftSum, hleftSumCan, hleftSumExact⟩
  rcases root_m31_add_corresponds right.a right.b hright.1 hright.2 with
    ⟨rightSum, hrightSum, hrightSumCan, hrightSumExact⟩
  rcases root_m31_mul_corresponds leftSum rightSum hleftSumCan hrightSumCan with
    ⟨m2, hm2, hm2Can, hm2Exact⟩
  rcases root_m31_sub_corresponds m0 m1 hm0Can hm1Can with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases root_m31_sub_corresponds m2 m0 hm2Can hm0Can with
    ⟨imagPartial, himagPartial, himagPartialCan, himagPartialExact⟩
  rcases root_m31_sub_corresponds imagPartial m1 himagPartialCan hm1Can with
    ⟨imag, himag, himagCan, himagExact⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩, ?_⟩
  · simp [_root_.aspis_core.field.CM31.mul,
      AuthenticFieldPow.field.CM31.mul,
      hm0, hm1, hleftSum, hrightSum, hm2,
      hreal, himagPartial, himag]
  · apply QuadraticAlgebra.ext
    · simp only [rootCM31ToExact, QuadraticAlgebra.re_mul]
      rw [hrealExact, hm0Exact, hm1Exact]
      ring
    · simp only [rootCM31ToExact, QuadraticAlgebra.im_mul]
      rw [himagExact, himagPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

theorem root_cm31_double_corresponds (value : RootCM31)
    (hvalue : CanonicalRootCM31 value) :
    ∃ output : RootCM31,
      AuthenticFieldPow.field.CM31.double
        { a := value.a, b := value.b } = .ok
          { a := output.a, b := output.b } ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact value + rootCM31ToExact value := by
  rcases root_m31_add_corresponds value.a value.a hvalue.1 hvalue.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases root_m31_add_corresponds value.b value.b hvalue.2 hvalue.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AuthenticFieldPow.field.CM31.double,
      AuthenticFieldPow.field.M31.double, hcallA, hcallB,
      _root_.aspis_core.field.M31.add]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem root_mul_by_r_corresponds (value : RootCM31)
    (hvalue : CanonicalRootCM31 value) :
    ∃ output : RootCM31,
      AuthenticFieldPow.field.mul_by_r
        { a := value.a, b := value.b } = .ok
          { a := output.a, b := output.b } ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = qm31R * rootCM31ToExact value := by
  rcases root_m31_add_corresponds value.a value.a hvalue.1 hvalue.1 with
    ⟨twoA, htwoA, htwoACan, htwoAExact⟩
  rcases root_m31_sub_corresponds twoA value.b htwoACan hvalue.2 with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases root_m31_add_corresponds value.b value.b hvalue.2 hvalue.2 with
    ⟨twoB, htwoB, htwoBCan, htwoBExact⟩
  rcases root_m31_add_corresponds value.a twoB hvalue.1 htwoBCan with
    ⟨imag, himag, himagCan, himagExact⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩, ?_⟩
  · simp [AuthenticFieldPow.field.mul_by_r,
      AuthenticFieldPow.field.M31.double,
      _root_.aspis_core.field.M31.add,
      htwoA, hreal, htwoB, himag]
  · apply QuadraticAlgebra.ext
    · simp only [rootCM31ToExact, qm31R, QuadraticAlgebra.re_mul]
      rw [hrealExact, htwoAExact]
      ring
    · simp only [rootCM31ToExact, qm31R, QuadraticAlgebra.im_mul]
      rw [himagExact, htwoBExact]
      ring

theorem root_qm31_add_corresponds (left right : RootQM31)
    (hleft : CanonicalRootQM31 left) (hright : CanonicalRootQM31 right) :
    ∃ output : RootQM31,
      _root_.aspis_core.field.QM31.add left right = .ok output ∧
      CanonicalRootQM31 output ∧
      rootQM31ToExact output = rootQM31ToExact left + rootQM31ToExact right := by
  rcases root_cm31_add_corresponds left.c0 right.c0 hleft.1 hright.1 with
    ⟨o0, hcall0, hcan0, hexact0⟩
  rcases root_cm31_add_corresponds left.c1 right.c1 hleft.2 hright.2 with
    ⟨o1, hcall1, hcan1, hexact1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [_root_.aspis_core.field.QM31.add, hcall0, hcall1]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

theorem root_qm31_sub_corresponds (left right : RootQM31)
    (hleft : CanonicalRootQM31 left) (hright : CanonicalRootQM31 right) :
    ∃ output : RootQM31,
      _root_.aspis_core.field.QM31.sub left right = .ok output ∧
      CanonicalRootQM31 output ∧
      rootQM31ToExact output = rootQM31ToExact left - rootQM31ToExact right := by
  rcases root_cm31_sub_corresponds left.c0 right.c0 hleft.1 hright.1 with
    ⟨o0, hcall0, hcan0, hexact0⟩
  rcases root_cm31_sub_corresponds left.c1 right.c1 hleft.2 hright.2 with
    ⟨o1, hcall1, hcan1, hexact1⟩
  refine ⟨⟨o0, o1⟩, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [_root_.aspis_core.field.QM31.sub,
      AspisCoreAdditive.field.QM31.sub,
      AspisCoreAdditive.field.CM31.sub, hcall0, hcall1]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

theorem root_qm31_mul_corresponds (left right : RootQM31)
    (hleft : CanonicalRootQM31 left) (hright : CanonicalRootQM31 right) :
    ∃ output : RootQM31,
      _root_.aspis_core.field.QM31.mul left right = .ok output ∧
      CanonicalRootQM31 output ∧
      rootQM31ToExact output = rootQM31ToExact left * rootQM31ToExact right := by
  rcases root_cm31_mul_corresponds left.c0 right.c0 hleft.1 hright.1 with
    ⟨m0, hm0, hm0Can, hm0Exact⟩
  rcases root_cm31_mul_corresponds left.c1 right.c1 hleft.2 hright.2 with
    ⟨m1, hm1, hm1Can, hm1Exact⟩
  rcases root_cm31_add_corresponds left.c0 left.c1 hleft.1 hleft.2 with
    ⟨leftSum, hleftSum, hleftSumCan, hleftSumExact⟩
  rcases root_cm31_add_corresponds right.c0 right.c1 hright.1 hright.2 with
    ⟨rightSum, hrightSum, hrightSumCan, hrightSumExact⟩
  rcases root_cm31_mul_corresponds leftSum rightSum hleftSumCan hrightSumCan with
    ⟨m2, hm2, hm2Can, hm2Exact⟩
  rcases root_mul_by_r_corresponds m1 hm1Can with
    ⟨rM1, hrM1, hrM1Can, hrM1Exact⟩
  rcases root_cm31_add_corresponds m0 rM1 hm0Can hrM1Can with
    ⟨low, hlow, hlowCan, hlowExact⟩
  rcases root_cm31_sub_corresponds m2 m0 hm2Can hm0Can with
    ⟨highPartial, hhighPartial, hhighPartialCan, hhighPartialExact⟩
  rcases root_cm31_sub_corresponds highPartial m1 hhighPartialCan hm1Can with
    ⟨high, hhigh, hhighCan, hhighExact⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hlowCan, hhighCan⟩, ?_⟩
  · simp [_root_.aspis_core.field.QM31.mul,
      AuthenticFieldPow.field.QM31.mul,
      hm0, hm1, hleftSum, hrightSum, hm2, hrM1,
      hlow, hhighPartial, hhigh]
  · apply QuadraticAlgebra.ext
    · simp only [rootQM31ToExact, QuadraticAlgebra.re_mul]
      rw [hlowExact, hm0Exact, hrM1Exact]
      ring
    · simp only [rootQM31ToExact, QuadraticAlgebra.im_mul]
      rw [hhighExact, hhighPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

def toRootCM31 (value : LocalCM31) : RootCM31 :=
  { a := value.a, b := value.b }

def fromRootCM31 (value : RootCM31) : LocalCM31 :=
  { a := value.a, b := value.b }

def toRootQM31 (value : LocalQM31) : RootQM31 :=
  { c0 := toRootCM31 value.c0, c1 := toRootCM31 value.c1 }

def fromRootQM31 (value : RootQM31) : LocalQM31 :=
  { c0 := fromRootCM31 value.c0, c1 := fromRootCM31 value.c1 }

@[simp] theorem root_exact_toRoot (value : LocalQM31) :
    rootQM31ToExact (toRootQM31 value) = qm31ToExact value := rfl

@[simp] theorem local_exact_fromRoot (value : RootQM31) :
    qm31ToExact (fromRootQM31 value) = rootQM31ToExact value := rfl

@[simp] theorem root_canonical_toRoot (value : LocalQM31) :
    CanonicalRootQM31 (toRootQM31 value) = CanonicalLocalQM31 value := rfl

@[simp] theorem local_canonical_fromRoot (value : RootQM31) :
    CanonicalLocalQM31 (fromRootQM31 value) = CanonicalRootQM31 value := rfl

theorem local_qm31_add_corresponds (left right : LocalQM31)
    (hleft : CanonicalLocalQM31 left) (hright : CanonicalLocalQM31 right) :
    ∃ output : LocalQM31,
      aspis_verifier.aspis_core.field.QM31.add left right = .ok output ∧
      CanonicalLocalQM31 output ∧
      qm31ToExact output = qm31ToExact left + qm31ToExact right := by
  rcases root_qm31_add_corresponds (toRootQM31 left) (toRootQM31 right)
      (by simpa using hleft) (by simpa using hright) with
    ⟨output, hcall, hcan, hexact⟩
  refine ⟨fromRootQM31 output, ?_, by simpa using hcan, ?_⟩
  · simpa [aspis_verifier.aspis_core.field.QM31.add,
      toRootQM31, fromRootQM31, toRootCM31, fromRootCM31] using hcall
  · simpa using hexact

theorem local_qm31_sub_corresponds (left right : LocalQM31)
    (hleft : CanonicalLocalQM31 left) (hright : CanonicalLocalQM31 right) :
    ∃ output : LocalQM31,
      aspis_verifier.aspis_core.field.QM31.sub left right = .ok output ∧
      CanonicalLocalQM31 output ∧
      qm31ToExact output = qm31ToExact left - qm31ToExact right := by
  rcases root_qm31_sub_corresponds (toRootQM31 left) (toRootQM31 right)
      (by simpa using hleft) (by simpa using hright) with
    ⟨output, hcall, hcan, hexact⟩
  refine ⟨fromRootQM31 output, ?_, by simpa using hcan, ?_⟩
  · simpa [aspis_verifier.aspis_core.field.QM31.sub,
      toRootQM31, fromRootQM31, toRootCM31, fromRootCM31] using hcall
  · simpa using hexact

theorem local_qm31_mul_corresponds (left right : LocalQM31)
    (hleft : CanonicalLocalQM31 left) (hright : CanonicalLocalQM31 right) :
    ∃ output : LocalQM31,
      aspis_verifier.aspis_core.field.QM31.mul left right = .ok output ∧
      CanonicalLocalQM31 output ∧
      qm31ToExact output = qm31ToExact left * qm31ToExact right := by
  rcases root_qm31_mul_corresponds (toRootQM31 left) (toRootQM31 right)
      (by simpa using hleft) (by simpa using hright) with
    ⟨output, hcall, hcan, hexact⟩
  refine ⟨fromRootQM31 output, ?_, by simpa using hcan, ?_⟩
  · simpa [aspis_verifier.aspis_core.field.QM31.mul,
      toRootQM31, fromRootQM31, toRootCM31, fromRootCM31] using hcall
  · simpa using hexact

theorem local_zero_call :
    aspis_verifier.aspis_core.field.QM31.ZERO = .ok
      { c0 := { a := 0#u32, b := 0#u32 },
        c1 := { a := 0#u32, b := 0#u32 } } := rfl

theorem local_one_call :
    aspis_verifier.aspis_core.field.QM31.ONE = .ok
      { c0 := { a := 1#u32, b := 0#u32 },
        c1 := { a := 0#u32, b := 0#u32 } } := rfl

theorem local_zero_canonical : CanonicalLocalQM31
    { c0 := { a := 0#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } } := by
  norm_num [CanonicalLocalQM31, CanonicalLocalCM31,
    CanonicalLocalM31, P]

theorem local_one_canonical : CanonicalLocalQM31
    { c0 := { a := 1#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } } := by
  norm_num [CanonicalLocalQM31, CanonicalLocalCM31,
    CanonicalLocalM31, P]

theorem local_zero_exact : qm31ToExact
    { c0 := { a := 0#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } } = 0 := by
  rfl

theorem local_one_exact : qm31ToExact
    { c0 := { a := 1#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } } = 1 := by
  rfl

private abbrev RootM31 := _root_.aspis_core.field.M31

private def preparedRow (a b sum : RootM31) :
    Array RootM31 3#usize :=
  Array.make 3#usize [a, b, sum]

def PreparedFor
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (left : LocalQM31) : Prop :=
  ∃ c0sum c1sum c01a c01b c01sum : RootM31,
    aspis_verifier.aspis_core.field.M31.add
      left.c0.a left.c0.b = .ok c0sum ∧
    aspis_verifier.aspis_core.field.M31.add
      left.c1.a left.c1.b = .ok c1sum ∧
    aspis_verifier.aspis_core.field.M31.add
      left.c0.a left.c1.a = .ok c01a ∧
    aspis_verifier.aspis_core.field.M31.add
      left.c0.b left.c1.b = .ok c01b ∧
    aspis_verifier.aspis_core.field.M31.add c01a c01b = .ok c01sum ∧
    CanonicalLocalM31 c0sum ∧
    CanonicalLocalM31 c1sum ∧
    CanonicalLocalM31 c01a ∧
    CanonicalLocalM31 c01b ∧
    CanonicalLocalM31 c01sum ∧
    (c0sum.val : ExactM31) =
      (left.c0.a.val : ExactM31) + (left.c0.b.val : ExactM31) ∧
    (c1sum.val : ExactM31) =
      (left.c1.a.val : ExactM31) + (left.c1.b.val : ExactM31) ∧
    (c01a.val : ExactM31) =
      (left.c0.a.val : ExactM31) + (left.c1.a.val : ExactM31) ∧
    (c01b.val : ExactM31) =
      (left.c0.b.val : ExactM31) + (left.c1.b.val : ExactM31) ∧
    (c01sum.val : ExactM31) =
      (c01a.val : ExactM31) + (c01b.val : ExactM31) ∧
    prepared.components = Array.make 3#usize [
      preparedRow left.c0.a left.c0.b c0sum,
      preparedRow left.c1.a left.c1.b c1sum,
      preparedRow c01a c01b c01sum]

theorem local_prepared_new_corresponds (left : LocalQM31)
    (hleft : CanonicalLocalQM31 left) :
    ∃ prepared : _root_.aspis_core.field.PreparedQm31Multiplier,
      aspis_verifier.aspis_core.field.PreparedQm31Multiplier.new left =
        .ok prepared ∧
      PreparedFor prepared left := by
  rcases local_m31_add_corresponds left.c0.a left.c0.b hleft.1.1 hleft.1.2 with
    ⟨c0sum, hc0sum, hc0sumCan, hc0sumExact⟩
  rcases local_m31_add_corresponds left.c1.a left.c1.b hleft.2.1 hleft.2.2 with
    ⟨c1sum, hc1sum, hc1sumCan, hc1sumExact⟩
  rcases local_m31_add_corresponds left.c0.a left.c1.a hleft.1.1 hleft.2.1 with
    ⟨c01a, hc01a, hc01aCan, hc01aExact⟩
  rcases local_m31_add_corresponds left.c0.b left.c1.b hleft.1.2 hleft.2.2 with
    ⟨c01b, hc01b, hc01bCan, hc01bExact⟩
  rcases local_m31_add_corresponds c01a c01b hc01aCan hc01bCan with
    ⟨c01sum, hc01sum, hc01sumCan, hc01sumExact⟩
  let prepared : _root_.aspis_core.field.PreparedQm31Multiplier := {
    components := Array.make 3#usize [
      preparedRow left.c0.a left.c0.b c0sum,
      preparedRow left.c1.a left.c1.b c1sum,
      preparedRow c01a c01b c01sum]
  }
  refine ⟨prepared, ?_, ?_⟩
  · simp [aspis_verifier.aspis_core.field.PreparedQm31Multiplier.new,
      hc0sum, hc1sum, hc01a, hc01b, hc01sum, preparedRow, prepared]
  · exact ⟨c0sum, c1sum, c01a, c01b, c01sum,
      hc0sum, hc1sum, hc01a, hc01b, hc01sum,
      hc0sumCan, hc1sumCan, hc01aCan, hc01bCan, hc01sumCan,
      hc0sumExact, hc1sumExact, hc01aExact, hc01bExact,
      hc01sumExact, rfl⟩

private def toAuthenticPreparedCM31 (value : RootCM31) :
    AuthenticFieldPreparedMul.field.CM31 :=
  { a := value.a, b := value.b }

private theorem prepared_row_mul_corresponds
    (left right : RootCM31) (leftSum : RootM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right)
    (hleftSum : CanonicalLocalM31 leftSum)
    (hleftSumExact : (leftSum.val : ExactM31) =
      (left.a.val : ExactM31) + (left.b.val : ExactM31)) :
    ∃ output : RootCM31,
      AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
          () (preparedRow left.a left.b leftSum,
            toAuthenticPreparedCM31 right) =
        .ok (toAuthenticPreparedCM31 output) ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact left * rootCM31ToExact right := by
  rcases root_m31_mul_corresponds left.a right.a hleft.1 hright.1 with
    ⟨m0, hm0, hm0Can, hm0Exact⟩
  rcases root_m31_mul_corresponds left.b right.b hleft.2 hright.2 with
    ⟨m1, hm1, hm1Can, hm1Exact⟩
  rcases root_m31_add_corresponds right.a right.b hright.1 hright.2 with
    ⟨rightSum, hrightSum, hrightSumCan, hrightSumExact⟩
  rcases root_m31_mul_corresponds leftSum rightSum hleftSum hrightSumCan with
    ⟨m2, hm2, hm2Can, hm2Exact⟩
  rcases root_m31_sub_corresponds m0 m1 hm0Can hm1Can with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases root_m31_sub_corresponds m2 m0 hm2Can hm0Can with
    ⟨imagPartial, himagPartial, himagPartialCan, himagPartialExact⟩
  rcases root_m31_sub_corresponds imagPartial m1 himagPartialCan hm1Can with
    ⟨imag, himag, himagCan, himagExact⟩
  let output : RootCM31 := { a := real, b := imag }
  refine ⟨output, ?_, ⟨hrealCan, himagCan⟩, ?_⟩
  · simp [AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
      preparedRow, toAuthenticPreparedCM31,
      _root_.aspis_core.field.M31.add,
      _root_.aspis_core.field.M31.sub,
      _root_.aspis_core.field.M31.mul,
      hm0, hm1, hrightSum, hm2, hreal, himagPartial, himag, output]
  · apply QuadraticAlgebra.ext
    · simp only [output, rootCM31ToExact, QuadraticAlgebra.re_mul]
      rw [hrealExact, hm0Exact, hm1Exact]
      ring
    · simp only [output, rootCM31ToExact, QuadraticAlgebra.im_mul]
      rw [himagExact, himagPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

theorem local_prepared_mul_corresponds
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (left right : LocalQM31)
    (hprepared : PreparedFor prepared left)
    (hleft : CanonicalLocalQM31 left)
    (hright : CanonicalLocalQM31 right) :
    ∃ output : LocalQM31,
      aspis_verifier.aspis_core.field.PreparedQm31Multiplier.mul
          prepared right = .ok output ∧
      CanonicalLocalQM31 output ∧
      qm31ToExact output = qm31ToExact left * qm31ToExact right := by
  rcases hprepared with ⟨c0sum, c1sum, c01a, c01b, c01sum,
    hc0sumCall, hc1sumCall, hc01aCall, hc01bCall, hc01sumCall,
    hc0sumCan, hc1sumCan, hc01aCan, hc01bCan, hc01sumCan,
    hc0sumExact, hc1sumExact, hc01aExact, hc01bExact, hc01sumExact,
    hcomponents⟩
  let left0 : RootCM31 := toRootCM31 left.c0
  let left1 : RootCM31 := toRootCM31 left.c1
  let right0 : RootCM31 := toRootCM31 right.c0
  let right1 : RootCM31 := toRootCM31 right.c1
  have hleft0 : CanonicalRootCM31 left0 := hleft.1
  have hleft1 : CanonicalRootCM31 left1 := hleft.2
  have hright0 : CanonicalRootCM31 right0 := hright.1
  have hright1 : CanonicalRootCM31 right1 := hright.2
  rcases prepared_row_mul_corresponds left0 right0 c0sum
      hleft0 hright0 hc0sumCan hc0sumExact with
    ⟨m0, hm0, hm0Can, hm0Exact⟩
  rcases prepared_row_mul_corresponds left1 right1 c1sum
      hleft1 hright1 hc1sumCan hc1sumExact with
    ⟨m1, hm1, hm1Can, hm1Exact⟩
  rcases root_cm31_add_corresponds right0 right1 hright0 hright1 with
    ⟨rightSum, hrightSum, hrightSumCan, hrightSumExact⟩
  let leftSum : RootCM31 := { a := c01a, b := c01b }
  have hleftSumCan : CanonicalRootCM31 leftSum := ⟨hc01aCan, hc01bCan⟩
  have hleftSumExact : rootCM31ToExact leftSum =
      rootCM31ToExact left0 + rootCM31ToExact left1 := by
    apply QuadraticAlgebra.ext
    · exact hc01aExact
    · exact hc01bExact
  rcases prepared_row_mul_corresponds leftSum rightSum c01sum
      hleftSumCan hrightSumCan hc01sumCan hc01sumExact with
    ⟨m2, hm2, hm2Can, hm2Exact⟩
  rcases root_mul_by_r_corresponds m1 hm1Can with
    ⟨rM1, hrM1, hrM1Can, hrM1Exact⟩
  rcases root_cm31_add_corresponds m0 rM1 hm0Can hrM1Can with
    ⟨low, hlow, hlowCan, hlowExact⟩
  rcases root_cm31_sub_corresponds m2 m0 hm2Can hm0Can with
    ⟨highPartial, hhighPartial, hhighPartialCan, hhighPartialExact⟩
  rcases root_cm31_sub_corresponds highPartial m1 hhighPartialCan hm1Can with
    ⟨high, hhigh, hhighCan, hhighExact⟩
  let rootOutput : RootQM31 := { c0 := low, c1 := high }
  let output : LocalQM31 := fromRootQM31 rootOutput
  refine ⟨output, ?_, ?_, ?_⟩
  · unfold aspis_verifier.aspis_core.field.PreparedQm31Multiplier.mul
    unfold _root_.aspis_core.field.PreparedQm31Multiplier.mul
    unfold AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul
    simp only [hcomponents]
    simp [preparedRow, toRootCM31, toRootQM31, fromRootCM31, fromRootQM31,
      toAuthenticPreparedCM31, left0, left1, right0, right1, leftSum,
      rootOutput, output, hm0, hm1, hrightSum, hm2, hrM1,
      hlow, hhighPartial, hhigh]
  · exact ⟨hlowCan, hhighCan⟩
  · apply QuadraticAlgebra.ext
    · simp only [output, rootOutput, local_exact_fromRoot,
        rootQM31ToExact, qm31ToExact, QuadraticAlgebra.re_mul]
      rw [hlowExact, hm0Exact, hrM1Exact, hm1Exact]
      ring
    · simp only [output, rootOutput, local_exact_fromRoot,
        rootQM31ToExact, qm31ToExact, QuadraticAlgebra.im_mul]
      rw [hhighExact, hhighPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

end GoodMatricesCurrent.SourceExtractedTerminalField
