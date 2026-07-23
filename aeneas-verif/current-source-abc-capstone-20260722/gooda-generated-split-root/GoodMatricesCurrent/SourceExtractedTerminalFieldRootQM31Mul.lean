import GoodMatricesCurrent.SourceExtractedTerminalFieldAuthenticPowCM31

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem root_qm31_mul_corresponds (left right : RootQM31)
    (hleft : CanonicalRootQM31 left) (hright : CanonicalRootQM31 right) :
    ∃ output : RootQM31,
      _root_.aspis_core.field.QM31.mul left right = .ok output ∧
      CanonicalRootQM31 output ∧
      rootQM31ToExact output = rootQM31ToExact left * rootQM31ToExact right := by
  rcases authentic_pow_cm31_mul_corresponds
      left.c0 right.c0 hleft.1 hright.1 with
    ⟨m0, hm0, hm0Can, hm0Exact⟩
  rcases authentic_pow_cm31_mul_corresponds
      left.c1 right.c1 hleft.2 hright.2 with
    ⟨m1, hm1, hm1Can, hm1Exact⟩
  rcases authentic_pow_cm31_add_corresponds
      left.c0 left.c1 hleft.1 hleft.2 with
    ⟨leftSum, hleftSum, hleftSumCan, hleftSumExact⟩
  rcases authentic_pow_cm31_add_corresponds
      right.c0 right.c1 hright.1 hright.2 with
    ⟨rightSum, hrightSum, hrightSumCan, hrightSumExact⟩
  rcases authentic_pow_cm31_mul_corresponds
      leftSum rightSum hleftSumCan hrightSumCan with
    ⟨m2, hm2, hm2Can, hm2Exact⟩
  rcases root_mul_by_r_corresponds m1 hm1Can with
    ⟨rM1, hrM1, hrM1Can, hrM1Exact⟩
  rcases authentic_pow_cm31_add_corresponds m0 rM1 hm0Can hrM1Can with
    ⟨low, hlow, hlowCan, hlowExact⟩
  rcases authentic_pow_cm31_sub_corresponds m2 m0 hm2Can hm0Can with
    ⟨highPartial, hhighPartial, hhighPartialCan, hhighPartialExact⟩
  rcases authentic_pow_cm31_sub_corresponds
      highPartial m1 hhighPartialCan hm1Can with
    ⟨high, hhigh, hhighCan, hhighExact⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hlowCan, hhighCan⟩, ?_⟩
  · rw [_root_.aspis_core.field.QM31.mul_eq_authentic]
    simp [AuthenticFieldPow.field.QM31.mul,
      hm0, hm1, hleftSum, hrightSum, hm2, hrM1,
      hlow, hhighPartial, hhigh]
  · apply QuadraticAlgebra.ext
    · simp only [rootQM31ToExact, QuadraticAlgebra.re_mul]
      rw [hlowExact, hm0Exact, hrM1Exact, hm1Exact]
      ring
    · simp only [rootQM31ToExact, QuadraticAlgebra.im_mul]
      rw [hhighExact, hhighPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

end GoodMatricesCurrent.SourceExtractedTerminalField
