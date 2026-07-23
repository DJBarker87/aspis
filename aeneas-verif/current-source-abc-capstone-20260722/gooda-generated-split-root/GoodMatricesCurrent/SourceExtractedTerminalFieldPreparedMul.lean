import GoodMatricesCurrent.SourceExtractedTerminalFieldPreparedRowMul
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootCM31Add
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootCM31Sub
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootMulByR

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

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
  have hrightSum' : AuthenticFieldPreparedMul.field.CM31.add
      (toAuthenticPreparedCM31 right0) (toAuthenticPreparedCM31 right1) =
        .ok (toAuthenticPreparedCM31 rightSum) := by
    simp only [toAuthenticPreparedCM31]
    rw [authentic_prepared_cm31_add_eq_root_mapped]
    simp [hrightSum]
  have hrM1' : AuthenticFieldPreparedMul.field.mul_by_r
      (toAuthenticPreparedCM31 m1) = .ok (toAuthenticPreparedCM31 rM1) := by
    simp only [toAuthenticPreparedCM31]
    rw [authentic_prepared_mul_by_r_eq_pow_mapped]
    simp [hrM1]
  have hlow' : AuthenticFieldPreparedMul.field.CM31.add
      (toAuthenticPreparedCM31 m0) (toAuthenticPreparedCM31 rM1) =
        .ok (toAuthenticPreparedCM31 low) := by
    simp only [toAuthenticPreparedCM31]
    rw [authentic_prepared_cm31_add_eq_root_mapped]
    simp [hlow]
  have hhighPartial' : AuthenticFieldPreparedMul.field.CM31.sub
      (toAuthenticPreparedCM31 m2) (toAuthenticPreparedCM31 m0) =
        .ok (toAuthenticPreparedCM31 highPartial) := by
    simp only [toAuthenticPreparedCM31]
    rw [authentic_prepared_cm31_sub_eq_root_mapped]
    simp [hhighPartial]
  have hhigh' : AuthenticFieldPreparedMul.field.CM31.sub
      (toAuthenticPreparedCM31 highPartial) (toAuthenticPreparedCM31 m1) =
        .ok (toAuthenticPreparedCM31 high) := by
    simp only [toAuthenticPreparedCM31]
    rw [authentic_prepared_cm31_sub_eq_root_mapped]
    simp [hhigh]
  let authenticOutput : AuthenticFieldPreparedMul.field.QM31 := {
    c0 := toAuthenticPreparedCM31 low,
    c1 := toAuthenticPreparedCM31 high
  }
  let rootOutput : RootQM31 := { c0 := low, c1 := high }
  have hm0' :
      AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (preparedRow left.c0.a left.c0.b c0sum,
          toAuthenticPreparedCM31 right0) =
        .ok (toAuthenticPreparedCM31 m0) := by
    simpa [left0, toRootCM31] using hm0
  have hm1' :
      AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (preparedRow left.c1.a left.c1.b c1sum,
          toAuthenticPreparedCM31 right1) =
        .ok (toAuthenticPreparedCM31 m1) := by
    simpa [left1, toRootCM31] using hm1
  have hm2' :
      AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (preparedRow c01a c01b c01sum,
          toAuthenticPreparedCM31 rightSum) =
        .ok (toAuthenticPreparedCM31 m2) := by
    simpa [leftSum] using hm2
  have hm0Literal :
      AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (Array.make 3#usize [left.c0.a, left.c0.b, c0sum],
          toAuthenticPreparedCM31 right0) =
        .ok (toAuthenticPreparedCM31 m0) := by
    simpa [preparedRow] using hm0'
  have hm1Literal :
      AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (Array.make 3#usize [left.c1.a, left.c1.b, c1sum],
          toAuthenticPreparedCM31 right1) =
        .ok (toAuthenticPreparedCM31 m1) := by
    simpa [preparedRow] using hm1'
  have hm2Literal :
      AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (Array.make 3#usize [c01a, c01b, c01sum],
          toAuthenticPreparedCM31 rightSum) =
        .ok (toAuthenticPreparedCM31 m2) := by
    simpa [preparedRow] using hm2'
  have hauthentic :
      AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul
        { components := prepared.components }
        { c0 := toAuthenticPreparedCM31 right0,
          c1 := toAuthenticPreparedCM31 right1 } =
        .ok authenticOutput := by
    unfold AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul
    simp only [hcomponents]
    change (do
      let x0 ←
        AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
          () (Array.make 3#usize [left.c0.a, left.c0.b, c0sum],
            toAuthenticPreparedCM31 right0)
      let x1 ←
        AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
          () (Array.make 3#usize [left.c1.a, left.c1.b, c1sum],
            toAuthenticPreparedCM31 right1)
      let rightTotal ← AuthenticFieldPreparedMul.field.CM31.add
        (toAuthenticPreparedCM31 right0)
        (toAuthenticPreparedCM31 right1)
      let x2 ←
        AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
          () (Array.make 3#usize [c01a, c01b, c01sum], rightTotal)
      let rx1 ← AuthenticFieldPreparedMul.field.mul_by_r x1
      let lo ← AuthenticFieldPreparedMul.field.CM31.add x0 rx1
      let hi0 ← AuthenticFieldPreparedMul.field.CM31.sub x2 x0
      let hi ← AuthenticFieldPreparedMul.field.CM31.sub hi0 x1
      .ok ({ c0 := lo, c1 := hi } : AuthenticFieldPreparedMul.field.QM31)) =
        .ok authenticOutput
    simp [hm0Literal, hm1Literal, hrightSum', hm2Literal,
      hrM1', hlow', hhighPartial', hhigh', authenticOutput]
  have hauthentic' :
      AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul
        { components := prepared.components }
        { c0 := { a := right0.a, b := right0.b },
          c1 := { a := right1.a, b := right1.b } } =
        .ok ({
          c0 := { a := low.a, b := low.b },
          c1 := { a := high.a, b := high.b }
        } : AuthenticFieldPreparedMul.field.QM31) := by
    simpa [toAuthenticPreparedCM31, authenticOutput] using hauthentic
  have hroot : _root_.aspis_core.field.PreparedQm31Multiplier.mul
      prepared { c0 := right0, c1 := right1 } = .ok rootOutput := by
    rw [_root_.aspis_core.field.PreparedQm31Multiplier.mul_eq_authentic]
    simp [hauthentic', rootOutput]
  have hroot' : _root_.aspis_core.field.PreparedQm31Multiplier.mul
      prepared
        { c0 := { a := right.c0.a, b := right.c0.b },
          c1 := { a := right.c1.a, b := right.c1.b } } =
        .ok ({ c0 := low, c1 := high } : RootQM31) := by
    simpa [right0, right1, toRootCM31, rootOutput] using hroot
  let output : LocalQM31 := fromRootQM31 rootOutput
  refine ⟨output, ?_, ?_, ?_⟩
  · rw [aspis_verifier.aspis_core.field.PreparedQm31Multiplier.mul_eq_current]
    simp [hroot',
      rootOutput, output, fromRootQM31, fromRootCM31]
  · exact ⟨hlowCan, hhighCan⟩
  · apply QuadraticAlgebra.ext
    · simp only [output, rootOutput, fromRootQM31, fromRootCM31,
        rootQM31ToExact, qm31ToExact, QuadraticAlgebra.re_mul]
      change rootCM31ToExact low =
        rootCM31ToExact left0 * rootCM31ToExact right0 +
          AspisV5ComponentCQM31TowerExact.qm31R *
            rootCM31ToExact left1 * rootCM31ToExact right1
      rw [hlowExact, hm0Exact, hrM1Exact, hm1Exact]
      ring
    · simp only [output, rootOutput, fromRootQM31, fromRootCM31,
        rootQM31ToExact, qm31ToExact, QuadraticAlgebra.im_mul]
      change rootCM31ToExact high =
        rootCM31ToExact left0 * rootCM31ToExact right1 +
          rootCM31ToExact left1 * rootCM31ToExact right0 +
            0 * rootCM31ToExact left1 * rootCM31ToExact right1
      rw [hhighExact, hhighPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

end GoodMatricesCurrent.SourceExtractedTerminalField
