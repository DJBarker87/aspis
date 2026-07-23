import GoodMatricesCurrent.SourceExtractedTerminalFieldLocalQM31Add
import GoodMatricesCurrent.SourceExtractedTerminalFieldLocalQM31Sub
import GoodMatricesCurrent.SourceExtractedTerminalFieldLocalQM31Mul

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem local_zero_call :
    aspis_verifier.aspis_core.field.QM31.ZERO = .ok
      { c0 := { a := 0#u32, b := 0#u32 },
        c1 := { a := 0#u32, b := 0#u32 } } := rfl

theorem local_one_call :
    aspis_verifier.aspis_core.field.QM31.ONE = .ok
      { c0 := { a := 1#u32, b := 0#u32 },
        c1 := { a := 0#u32, b := 0#u32 } } := rfl

theorem local_zero_canonical : CanonicalLocalQM31
    { c0 := { a := 0#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } } := by
  norm_num [CanonicalLocalQM31, CanonicalLocalCM31,
    CanonicalLocalM31, AspisV5ComponentCQM31TowerExact.P]

theorem local_one_canonical : CanonicalLocalQM31
    { c0 := { a := 1#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } } := by
  norm_num [CanonicalLocalQM31, CanonicalLocalCM31,
    CanonicalLocalM31, AspisV5ComponentCQM31TowerExact.P]

theorem local_zero_exact : qm31ToExact
    { c0 := { a := 0#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } } = 0 := by
  rfl

theorem local_one_exact : qm31ToExact
    { c0 := { a := 1#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } } = 1 := by
  rfl

end GoodMatricesCurrent.SourceExtractedTerminalField
