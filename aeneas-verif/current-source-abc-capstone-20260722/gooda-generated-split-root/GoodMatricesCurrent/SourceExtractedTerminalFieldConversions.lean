import GoodMatricesCurrent.SourceExtractedTerminalFieldRootQM31Add
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootQM31Sub
import GoodMatricesCurrent.SourceExtractedTerminalFieldRootQM31Mul

namespace GoodMatricesCurrent.SourceExtractedTerminalField

def toRootCM31 (value : LocalCM31) : RootCM31 :=
  { a := value.a, b := value.b }

def fromRootCM31 (value : RootCM31) : LocalCM31 :=
  { a := value.a, b := value.b }

def toRootQM31 (value : LocalQM31) : RootQM31 :=
  { c0 := toRootCM31 value.c0, c1 := toRootCM31 value.c1 }

def fromRootQM31 (value : RootQM31) : LocalQM31 :=
  { c0 := fromRootCM31 value.c0, c1 := fromRootCM31 value.c1 }

@[simp] theorem root_exact_toRoot (value : LocalQM31) :
    rootQM31ToExact (toRootQM31 value) = qm31ToExact value := rfl

@[simp] theorem local_exact_fromRoot (value : RootQM31) :
    qm31ToExact (fromRootQM31 value) = rootQM31ToExact value := rfl

@[simp] theorem root_canonical_toRoot (value : LocalQM31) :
    CanonicalRootQM31 (toRootQM31 value) = CanonicalLocalQM31 value := rfl

@[simp] theorem local_canonical_fromRoot (value : RootQM31) :
    CanonicalLocalQM31 (fromRootQM31 value) = CanonicalRootQM31 value := rfl

end GoodMatricesCurrent.SourceExtractedTerminalField
