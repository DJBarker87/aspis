import GoodMatricesCurrent.SourceExtractedTerminalField

namespace GoodMatricesCurrent.SourceExtractedTerminalField

abbrev RootCM31 := _root_.aspis_core.field.CM31
abbrev RootQM31 := _root_.aspis_core.field.QM31

def CanonicalRootCM31 (value : RootCM31) : Prop :=
  CanonicalLocalM31 value.a ∧ CanonicalLocalM31 value.b

def CanonicalRootQM31 (value : RootQM31) : Prop :=
  CanonicalRootCM31 value.c0 ∧ CanonicalRootCM31 value.c1

def rootCM31ToExact (value : RootCM31) : ExactCM31 :=
  ⟨(value.a.val : ExactM31), (value.b.val : ExactM31)⟩

def rootQM31ToExact (value : RootQM31) : ExactQM31 :=
  ⟨rootCM31ToExact value.c0, rootCM31ToExact value.c1⟩

end GoodMatricesCurrent.SourceExtractedTerminalField
