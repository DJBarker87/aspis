import AspisFormal.Pool.V7PackedFibreLayout
import AspisFormal.V5ComponentCQM31TowerExact

/-!
# Canonical packed fibres to the exact deployed QM31 tower

The memory-heavy field tower is isolated in this tiny bridge. Byte packing,
canonicality and layout have already been kernel-checked in smaller modules;
this file performs only the literal four-coordinate conversion.
-/

set_option autoImplicit false

namespace AspisPool.V7PackedFibreTowerBridge

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7PackedLimbDecoder
open AspisPool.V7PackedFibreIndices
open AspisPool.V7CanonicalQM31
open AspisPool.V7PackedC1Entry
open AspisPool.V7PackedC2Entry
open AspisV5ComponentCQM31TowerExact

def canonicalM31ToExact (value : CanonicalM31) : M31Exact := value.val

def canonicalQM31ToExact (value : CanonicalQM31) : QM31Exact :=
  ⟨⟨canonicalM31ToExact value.c0a, canonicalM31ToExact value.c0b⟩,
    ⟨canonicalM31ToExact value.c1a, canonicalM31ToExact value.c1b⟩⟩

def decodeC1EntryExact (value : C1Value) (slot : Fin 4)
    (column : Fin 26) : Option M31Exact :=
  (decodeC1Entry value slot column).map canonicalM31ToExact

def decodeC2EntryExact (value : C2Value) (helper : Fin 3)
    (slot : Fin 4) : Option QM31Exact :=
  (decodeC2Entry value helper slot).map canonicalQM31ToExact

theorem canonicalQM31ToExact_literal_order (value : CanonicalQM31) :
    canonicalQM31ToExact value =
      ⟨⟨(value.c0a.val : M31Exact), (value.c0b.val : M31Exact)⟩,
        ⟨(value.c1a.val : M31Exact), (value.c1b.val : M31Exact)⟩⟩ := rfl

theorem decoded_c2_exact_has_deployed_tower_order
    (value : C2Value) (helper : Fin 3) (slot : Fin 4)
    (a b c d : CanonicalM31)
    (decoded : decodeC2Entry value helper slot = some ⟨a, b, c, d⟩) :
    decodeC2EntryExact value helper slot =
      some ⟨⟨(a.val : M31Exact), (b.val : M31Exact)⟩,
        ⟨(c.val : M31Exact), (d.val : M31Exact)⟩⟩ := by
  simp [decodeC2EntryExact, decoded, canonicalQM31ToExact, canonicalM31ToExact]

#print axioms canonicalQM31ToExact_literal_order
#print axioms decoded_c2_exact_has_deployed_tower_order

end AspisPool.V7PackedFibreTowerBridge
