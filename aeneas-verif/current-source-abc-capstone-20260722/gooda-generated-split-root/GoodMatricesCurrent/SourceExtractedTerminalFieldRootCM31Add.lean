import GoodMatricesCurrent.SourceExtractedTerminalFieldTypes
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootM31Add

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

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

end GoodMatricesCurrent.SourceExtractedTerminalField
