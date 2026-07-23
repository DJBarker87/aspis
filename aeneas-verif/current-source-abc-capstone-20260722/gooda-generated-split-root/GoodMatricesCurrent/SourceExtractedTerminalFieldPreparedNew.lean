import GoodMatricesCurrent.SourceExtractedTerminalFieldPreparedTypes

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

theorem local_prepared_new_corresponds (left : LocalQM31)
    (hleft : CanonicalLocalQM31 left) :
    ∃ prepared : _root_.aspis_core.field.PreparedQm31Multiplier,
      aspis_verifier.aspis_core.field.PreparedQm31Multiplier.new left =
        .ok prepared ∧
      PreparedFor prepared left := by
  rcases local_m31_add_corresponds left.c0.a left.c0.b hleft.1.1 hleft.1.2 with
    ⟨c0sum, hc0sum, hc0sumCan, hc0sumExact⟩
  rcases local_m31_add_corresponds left.c1.a left.c1.b hleft.2.1 hleft.2.2 with
    ⟨c1sum, hc1sum, hc1sumCan, hc1sumExact⟩
  rcases local_m31_add_corresponds left.c0.a left.c1.a hleft.1.1 hleft.2.1 with
    ⟨c01a, hc01a, hc01aCan, hc01aExact⟩
  rcases local_m31_add_corresponds left.c0.b left.c1.b hleft.1.2 hleft.2.2 with
    ⟨c01b, hc01b, hc01bCan, hc01bExact⟩
  rcases local_m31_add_corresponds c01a c01b hc01aCan hc01bCan with
    ⟨c01sum, hc01sum, hc01sumCan, hc01sumExact⟩
  let prepared : _root_.aspis_core.field.PreparedQm31Multiplier := {
    components := Array.make 3#usize [
      preparedRow left.c0.a left.c0.b c0sum,
      preparedRow left.c1.a left.c1.b c1sum,
      preparedRow c01a c01b c01sum]
  }
  refine ⟨prepared, ?_, ?_⟩
  · simp [aspis_verifier.aspis_core.field.PreparedQm31Multiplier.new,
      hc0sum, hc1sum, hc01a, hc01b, hc01sum, preparedRow, prepared]
  · exact ⟨c0sum, c1sum, c01a, c01b, c01sum,
      hc0sum, hc1sum, hc01a, hc01b, hc01sum,
      hc0sumCan, hc1sumCan, hc01aCan, hc01bCan, hc01sumCan,
      hc0sumExact, hc1sumExact, hc01aExact, hc01bExact,
      hc01sumExact, rfl⟩

end GoodMatricesCurrent.SourceExtractedTerminalField
