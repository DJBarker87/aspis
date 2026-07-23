import GoodMatricesCurrent.SourceExtractedTerminalField
import GoodMatricesCurrent.SourceExtractedAuthenticM31Sub

open Aeneas Aeneas.Std Result

namespace ProbeAdapter

theorem sub_eq (a b : Std.U32) :
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

example (left right : _root_.aspis_core.field.M31)
    (hleft : GoodMatricesCurrent.SourceExtractedTerminalField.CanonicalLocalM31 left)
    (hright : GoodMatricesCurrent.SourceExtractedTerminalField.CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.sub left right = .ok output ∧
      GoodMatricesCurrent.SourceExtractedTerminalField.CanonicalLocalM31 output ∧
      (output.val : GoodMatricesCurrent.SourceExtractedTerminalField.ExactM31) =
        (left.val : GoodMatricesCurrent.SourceExtractedTerminalField.ExactM31) -
          (right.val : GoodMatricesCurrent.SourceExtractedTerminalField.ExactM31) := by
  rcases GoodMatricesCurrent.SourceExtractedAuthenticM31Sub.extracted_m31_sub_corresponds
      left right hleft hright with ⟨output, hcall, hcan, hexact⟩
  refine ⟨output, ?_, hcan, hexact⟩
  unfold _root_.aspis_core.field.M31.sub
  rw [sub_eq]
  exact hcall

end ProbeAdapter

set_option pp.privateNames true in
#print _root_.aspis_core.field.CM31.sub

example (left right : _root_.aspis_core.field.CM31) :
    _root_.aspis_core.field.CM31.sub left right = (do
      let a ← _root_.aspis_core.field.M31.sub left.a right.a
      let b ← _root_.aspis_core.field.M31.sub left.b right.b
      .ok ({ a := a, b := b } : _root_.aspis_core.field.CM31)) := by
  cases left
  cases right
  rfl
