import GoodMatricesCurrent.SourceExtractedTerminalField

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem root_m31_add_corresponds (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.add left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) + (right.val : ExactM31) := by
  simpa [aspis_verifier.aspis_core.field.M31.add] using
    local_m31_add_corresponds left right hleft hright

end GoodMatricesCurrent.SourceExtractedTerminalField
