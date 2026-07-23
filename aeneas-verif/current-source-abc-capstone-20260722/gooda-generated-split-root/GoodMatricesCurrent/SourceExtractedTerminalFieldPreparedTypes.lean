import GoodMatricesCurrent.SourceExtractedTerminalFieldConstants

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedTerminalField

abbrev RootM31 := _root_.aspis_core.field.M31

def preparedRow (a b sum : RootM31) : Array RootM31 3#usize :=
  Array.make 3#usize [a, b, sum]

def PreparedFor
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (left : LocalQM31) : Prop :=
  ∃ c0sum c1sum c01a c01b c01sum : RootM31,
    aspis_verifier.aspis_core.field.M31.add
      left.c0.a left.c0.b = .ok c0sum ∧
    aspis_verifier.aspis_core.field.M31.add
      left.c1.a left.c1.b = .ok c1sum ∧
    aspis_verifier.aspis_core.field.M31.add
      left.c0.a left.c1.a = .ok c01a ∧
    aspis_verifier.aspis_core.field.M31.add
      left.c0.b left.c1.b = .ok c01b ∧
    aspis_verifier.aspis_core.field.M31.add c01a c01b = .ok c01sum ∧
    CanonicalLocalM31 c0sum ∧
    CanonicalLocalM31 c1sum ∧
    CanonicalLocalM31 c01a ∧
    CanonicalLocalM31 c01b ∧
    CanonicalLocalM31 c01sum ∧
    (c0sum.val : ExactM31) =
      (left.c0.a.val : ExactM31) + (left.c0.b.val : ExactM31) ∧
    (c1sum.val : ExactM31) =
      (left.c1.a.val : ExactM31) + (left.c1.b.val : ExactM31) ∧
    (c01a.val : ExactM31) =
      (left.c0.a.val : ExactM31) + (left.c1.a.val : ExactM31) ∧
    (c01b.val : ExactM31) =
      (left.c0.b.val : ExactM31) + (left.c1.b.val : ExactM31) ∧
    (c01sum.val : ExactM31) =
      (c01a.val : ExactM31) + (c01b.val : ExactM31) ∧
    prepared.components = Array.make 3#usize [
      preparedRow left.c0.a left.c0.b c0sum,
      preparedRow left.c1.a left.c1.b c1sum,
      preparedRow c01a c01b c01sum]

def toAuthenticPreparedCM31 (value : RootCM31) :
    AuthenticFieldPreparedMul.field.CM31 :=
  { a := value.a, b := value.b }

end GoodMatricesCurrent.SourceExtractedTerminalField
