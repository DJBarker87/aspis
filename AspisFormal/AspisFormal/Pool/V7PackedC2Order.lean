import AspisFormal.Pool.V7PackedC2Entry

/-! Kernel proof of the deployed C2 tower-limb order. -/

set_option autoImplicit false

namespace AspisPool.V7PackedC2Order

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7PackedLimbDecoder
open AspisPool.V7PackedFibreIndices
open AspisPool.V7CanonicalQM31
open AspisPool.V7PackedC2Entry

theorem decoded_c2_entry_has_literal_limb_order
    (value : C2Value) (helper : Fin 3) (slot : Fin 4)
    (a b c d : CanonicalM31)
    (ha : decodeC2PackedLimb value (c2LimbIndex helper slot 0) = some a)
    (hb : decodeC2PackedLimb value (c2LimbIndex helper slot 1) = some b)
    (hc : decodeC2PackedLimb value (c2LimbIndex helper slot 2) = some c)
    (hd : decodeC2PackedLimb value (c2LimbIndex helper slot 3) = some d) :
    decodeC2Entry value helper slot = some ⟨a, b, c, d⟩ := by
  unfold decodeC2Entry
  exact assembleC2Entry_of_eq_some _ _ _ _ a b c d ha hb hc hd

#print axioms decoded_c2_entry_has_literal_limb_order

end AspisPool.V7PackedC2Order
