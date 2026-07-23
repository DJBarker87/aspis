import GoodMatricesCurrent.SourceExtractedTerminalFieldPreparedNew
import GoodMatricesCurrent.SourceExtractedTerminalFieldAuthenticPreparedBridge

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem prepared_row_mul_corresponds
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
  have hm0' : AuthenticFieldPreparedMul.field.M31.mul left.a right.a =
      .ok m0 := by
    rw [← root_m31_mul_eq_authentic_prepared]
    exact hm0
  have hm1' : AuthenticFieldPreparedMul.field.M31.mul left.b right.b =
      .ok m1 := by
    rw [← root_m31_mul_eq_authentic_prepared]
    exact hm1
  have hrightSum' : AuthenticFieldPreparedMul.field.M31.add
      right.a right.b = .ok rightSum := by
    rw [← root_m31_add_eq_authentic_prepared]
    exact hrightSum
  have hm2' : AuthenticFieldPreparedMul.field.M31.mul leftSum rightSum =
      .ok m2 := by
    rw [← root_m31_mul_eq_authentic_prepared]
    exact hm2
  have hreal' : AuthenticFieldPreparedMul.field.M31.sub m0 m1 = .ok real := by
    rw [← root_m31_sub_eq_authentic_prepared]
    exact hreal
  have himagPartial' : AuthenticFieldPreparedMul.field.M31.sub m2 m0 =
      .ok imagPartial := by
    rw [← root_m31_sub_eq_authentic_prepared]
    exact himagPartial
  have himag' : AuthenticFieldPreparedMul.field.M31.sub imagPartial m1 =
      .ok imag := by
    rw [← root_m31_sub_eq_authentic_prepared]
    exact himag
  let output : RootCM31 := { a := real, b := imag }
  refine ⟨output, ?_, ⟨hrealCan, himagCan⟩, ?_⟩
  · simp [AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
      preparedRow, toAuthenticPreparedCM31, Array.index_usize, Array.make,
      hm0', hm1', hrightSum', hm2', hreal', himagPartial', himag', output]
  · apply QuadraticAlgebra.ext
    · simp only [output, rootCM31ToExact, QuadraticAlgebra.re_mul]
      rw [hrealExact, hm0Exact, hm1Exact]
      ring
    · simp only [output, rootCM31ToExact, QuadraticAlgebra.im_mul]
      rw [himagExact, himagPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

end GoodMatricesCurrent.SourceExtractedTerminalField
