import GoodMatricesCurrent.SourceExtractedTerminalFieldConversions

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem local_qm31_add_corresponds (left right : LocalQM31)
    (hleft : CanonicalLocalQM31 left) (hright : CanonicalLocalQM31 right) :
    ∃ output : LocalQM31,
      aspis_verifier.aspis_core.field.QM31.add left right = .ok output ∧
      CanonicalLocalQM31 output ∧
      qm31ToExact output = qm31ToExact left + qm31ToExact right := by
  rcases root_qm31_add_corresponds (toRootQM31 left) (toRootQM31 right)
      (by simpa using hleft) (by simpa using hright) with
    ⟨output, hcall, hcan, hexact⟩
  have hcall' : _root_.aspis_core.field.QM31.add
      { c0 := { a := left.c0.a, b := left.c0.b },
        c1 := { a := left.c1.a, b := left.c1.b } }
      { c0 := { a := right.c0.a, b := right.c0.b },
        c1 := { a := right.c1.a, b := right.c1.b } } = .ok output := by
    simpa [toRootQM31, toRootCM31] using hcall
  refine ⟨fromRootQM31 output, ?_, by simpa using hcan, ?_⟩
  · rw [aspis_verifier.aspis_core.field.QM31.add_eq_current]
    simp [fromRootQM31, fromRootCM31, hcall']
  · simpa using hexact

end GoodMatricesCurrent.SourceExtractedTerminalField
