import GoodMatricesCurrent.SourceExtractedTerminalFieldRootCM31Add

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

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

end GoodMatricesCurrent.SourceExtractedTerminalField
