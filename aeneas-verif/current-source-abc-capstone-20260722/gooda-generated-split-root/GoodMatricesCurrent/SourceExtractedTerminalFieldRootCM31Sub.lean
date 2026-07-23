import GoodMatricesCurrent.SourceExtractedTerminalFieldTypes
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootM31Sub

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem authentic_sub_cm31_corresponds (left right : RootCM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right) :
    ∃ output : RootCM31,
      AspisCoreAdditive.field.CM31.sub
        { a := left.a, b := left.b } { a := right.a, b := right.b } =
          .ok { a := output.a, b := output.b } ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact left - rootCM31ToExact right := by
  rcases root_m31_sub_corresponds left.a right.a hleft.1 hright.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases root_m31_sub_corresponds left.b right.b hleft.2 hright.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  have hcallA' :
      AspisCoreAdditive.field.M31.sub left.a right.a = .ok oa := by
    simpa [_root_.aspis_core.field.M31.sub] using hcallA
  have hcallB' :
      AspisCoreAdditive.field.M31.sub left.b right.b = .ok ob := by
    simpa [_root_.aspis_core.field.M31.sub] using hcallB
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AspisCoreAdditive.field.CM31.sub, hcallA', hcallB']
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem root_cm31_sub_corresponds (left right : RootCM31)
    (hleft : CanonicalRootCM31 left) (hright : CanonicalRootCM31 right) :
    ∃ output : RootCM31,
      _root_.aspis_core.field.CM31.sub left right = .ok output ∧
      CanonicalRootCM31 output ∧
      rootCM31ToExact output = rootCM31ToExact left - rootCM31ToExact right := by
  rcases authentic_sub_cm31_corresponds left right hleft hright with
    ⟨output, hcall, hcan, hexact⟩
  refine ⟨output, ?_, hcan, hexact⟩
  rw [_root_.aspis_core.field.CM31.sub_eq_authentic]
  simp [hcall]

end GoodMatricesCurrent.SourceExtractedTerminalField
