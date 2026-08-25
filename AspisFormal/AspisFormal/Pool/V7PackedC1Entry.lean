import AspisFormal.Pool.V7PackedFibreIndices

/-! Exact C1 slot-major entry decoder. -/

set_option autoImplicit false

namespace AspisPool.V7PackedC1Entry

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7PackedLimbDecoder
open AspisPool.V7PackedFibreIndices

def decodeC1Entry (value : C1Value) (slot : Fin 4)
    (column : Fin 26) : Option CanonicalM31 :=
  decodeC1PackedLimb value (c1LimbIndex slot column)

theorem decodeC1Entry_exact (value : C1Value) (slot : Fin 4)
    (column : Fin 26) :
    decodeC1Entry value slot column =
      decodeC1PackedLimb value (c1LimbIndex slot column) := rfl

#print axioms decodeC1Entry_exact

end AspisPool.V7PackedC1Entry
