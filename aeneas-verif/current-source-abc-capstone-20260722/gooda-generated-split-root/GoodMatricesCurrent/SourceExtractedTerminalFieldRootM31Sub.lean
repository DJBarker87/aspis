import GoodMatricesCurrent.SourceExtractedTerminalField
import GoodMatricesCurrent.SourceExtractedAuthenticM31Sub

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem authentic_sub_eq_generated_cm31_sub (a b : Std.U32) :
    AspisCoreAdditive.field.M31.sub a b =
      AspisCoreCM31Multiplicative.field.M31.sub a b := by
  have hP : AspisCoreAdditive.field.P =
      AspisCoreCM31Multiplicative.field.P := by
    apply UScalar.eq_of_val_eq
    unfold AspisCoreAdditive.field.P AspisCoreCM31Multiplicative.field.P
    rfl
  unfold AspisCoreAdditive.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [hP]

theorem root_m31_sub_corresponds (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.sub left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) - (right.val : ExactM31) := by
  rcases GoodMatricesCurrent.SourceExtractedAuthenticM31Sub.extracted_m31_sub_corresponds
      left right hleft hright with ⟨output, hcall, hcan, hexact⟩
  refine ⟨output, ?_, hcan, hexact⟩
  unfold _root_.aspis_core.field.M31.sub
  rw [authentic_sub_eq_generated_cm31_sub]
  exact hcall

end GoodMatricesCurrent.SourceExtractedTerminalField
