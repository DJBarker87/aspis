import GoodMatricesCurrent.SourceExtractedTerminalFieldRootCM31Add
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootCM31Sub
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootM31Mul
import GoodMatricesCurrent.SourceExtractedTerminalFieldAuthenticPowBridge

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem authentic_pow_cm31_mul_corresponds (left right : RootCM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right) :
    ∃ output : RootCM31,
      AuthenticFieldPow.field.CM31.mul
        { a := left.a, b := left.b } { a := right.a, b := right.b } =
          .ok { a := output.a, b := output.b } ∧
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
  have hm0' : AuthenticFieldPow.field.M31.mul left.a right.a = .ok m0 := by
    rw [← root_m31_mul_eq_authentic_pow]
    exact hm0
  have hm1' : AuthenticFieldPow.field.M31.mul left.b right.b = .ok m1 := by
    rw [← root_m31_mul_eq_authentic_pow]
    exact hm1
  have hleftSum' : AuthenticFieldPow.field.M31.add left.a left.b =
      .ok leftSum := by
    rw [← root_m31_add_eq_authentic_pow]
    exact hleftSum
  have hrightSum' : AuthenticFieldPow.field.M31.add right.a right.b =
      .ok rightSum := by
    rw [← root_m31_add_eq_authentic_pow]
    exact hrightSum
  have hm2' : AuthenticFieldPow.field.M31.mul leftSum rightSum = .ok m2 := by
    rw [← root_m31_mul_eq_authentic_pow]
    exact hm2
  have hreal' : AuthenticFieldPow.field.M31.sub m0 m1 = .ok real := by
    rw [← root_m31_sub_eq_authentic_pow]
    exact hreal
  have himagPartial' : AuthenticFieldPow.field.M31.sub m2 m0 =
      .ok imagPartial := by
    rw [← root_m31_sub_eq_authentic_pow]
    exact himagPartial
  have himag' : AuthenticFieldPow.field.M31.sub imagPartial m1 = .ok imag := by
    rw [← root_m31_sub_eq_authentic_pow]
    exact himag
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩, ?_⟩
  · simp [AuthenticFieldPow.field.CM31.mul,
      hm0', hm1', hleftSum', hrightSum', hm2',
      hreal', himagPartial', himag']
  · apply QuadraticAlgebra.ext
    · simp only [rootCM31ToExact, QuadraticAlgebra.re_mul]
      rw [hrealExact, hm0Exact, hm1Exact]
      ring
    · simp only [rootCM31ToExact, QuadraticAlgebra.im_mul]
      rw [himagExact, himagPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

theorem root_cm31_mul_corresponds (left right : RootCM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right) :
    ∃ output : RootCM31,
      _root_.aspis_core.field.CM31.mul left right = .ok output ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact left * rootCM31ToExact right := by
  rcases authentic_pow_cm31_mul_corresponds left right hleft hright with
    ⟨output, hcall, hcan, hexact⟩
  refine ⟨output, ?_, hcan, hexact⟩
  rw [_root_.aspis_core.field.CM31.mul_eq_authentic]
  simp [hcall]

end GoodMatricesCurrent.SourceExtractedTerminalField
