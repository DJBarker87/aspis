import GoodMatricesCurrent.SourceExtractedTerminalField

open Aeneas Aeneas.Std Result ControlFlow Error

namespace GoodMatricesCurrent.SourceExtractedTerminalField

def rootM31SubOutput (left right : _root_.aspis_core.field.M31) :
    _root_.aspis_core.field.M31 :=
  let reduced := Std.U32.wrapping_sub
    (Std.U32.wrapping_add left 2147483647#u32) right
  if reduced >= 2147483647#u32 then
    Std.U32.wrapping_sub reduced 2147483647#u32
  else reduced

theorem root_m31_sub_call (left right : _root_.aspis_core.field.M31) :
    _root_.aspis_core.field.M31.sub left right =
      .ok (rootM31SubOutput left right) := by
  unfold _root_.aspis_core.field.M31.sub
  unfold AspisCoreAdditive.field.M31.sub
  simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
  rw [AspisCoreAdditive.field.P]
  rfl

end GoodMatricesCurrent.SourceExtractedTerminalField
