import GoodMatricesCurrent.SourceExtractedTerminalFieldRootCM31Mul
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootMulByR

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem authentic_pow_cm31_add_corresponds (left right : RootCM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right) :
    ∃ output : RootCM31,
      AuthenticFieldPow.field.CM31.add
        { a := left.a, b := left.b } { a := right.a, b := right.b } =
          .ok { a := output.a, b := output.b } ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact left + rootCM31ToExact right := by
  rcases root_m31_add_corresponds left.a right.a hleft.1 hright.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases root_m31_add_corresponds left.b right.b hleft.2 hright.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  have hcallA' : AuthenticFieldPow.field.M31.add left.a right.a = .ok oa := by
    rw [← root_m31_add_eq_authentic_pow]
    exact hcallA
  have hcallB' : AuthenticFieldPow.field.M31.add left.b right.b = .ok ob := by
    rw [← root_m31_add_eq_authentic_pow]
    exact hcallB
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AuthenticFieldPow.field.CM31.add, hcallA', hcallB']
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem authentic_pow_cm31_sub_corresponds (left right : RootCM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right) :
    ∃ output : RootCM31,
      AuthenticFieldPow.field.CM31.sub
        { a := left.a, b := left.b } { a := right.a, b := right.b } =
          .ok { a := output.a, b := output.b } ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact left - rootCM31ToExact right := by
  rcases root_m31_sub_corresponds left.a right.a hleft.1 hright.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases root_m31_sub_corresponds left.b right.b hleft.2 hright.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  have hcallA' : AuthenticFieldPow.field.M31.sub left.a right.a = .ok oa := by
    rw [← root_m31_sub_eq_authentic_pow]
    exact hcallA
  have hcallB' : AuthenticFieldPow.field.M31.sub left.b right.b = .ok ob := by
    rw [← root_m31_sub_eq_authentic_pow]
    exact hcallB
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AuthenticFieldPow.field.CM31.sub, hcallA', hcallB']
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

end GoodMatricesCurrent.SourceExtractedTerminalField
