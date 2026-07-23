import GoodMatricesCurrent.SourceExtractedTerminalFieldTypes

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem root_m31_add_eq_authentic_pow (left right : Std.U32) :
    _root_.aspis_core.field.M31.add left right =
      AuthenticFieldPow.field.M31.add left right := by
  have hP : _root_.aspis_core.field.P = AuthenticFieldPow.field.P := by
    apply UScalar.eq_of_val_eq
    unfold _root_.aspis_core.field.P AuthenticFieldPow.field.P
    rfl
  unfold _root_.aspis_core.field.M31.add AuthenticFieldPow.field.M31.add
  rw [hP]

theorem root_m31_sub_eq_authentic_pow (left right : Std.U32) :
    _root_.aspis_core.field.M31.sub left right =
      AuthenticFieldPow.field.M31.sub left right := by
  have hP : AspisCoreAdditive.field.P = AuthenticFieldPow.field.P := by
    apply UScalar.eq_of_val_eq
    unfold AspisCoreAdditive.field.P AuthenticFieldPow.field.P
    rfl
  unfold _root_.aspis_core.field.M31.sub
  unfold AspisCoreAdditive.field.M31.sub AuthenticFieldPow.field.M31.sub
  rw [hP]

theorem root_m31_mul_eq_authentic_pow (left right : Std.U32) :
    _root_.aspis_core.field.M31.mul left right =
      AuthenticFieldPow.field.M31.mul left right := by
  rfl

end GoodMatricesCurrent.SourceExtractedTerminalField
