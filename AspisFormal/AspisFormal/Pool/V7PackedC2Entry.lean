import AspisFormal.Pool.V7PackedFibreIndices
import AspisFormal.Pool.V7CanonicalQM31

/-! Exact helper-major C2 four-limb entry decoder. -/

set_option autoImplicit false

namespace AspisPool.V7PackedC2Entry

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7PackedLimbDecoder
open AspisPool.V7PackedFibreIndices
open AspisPool.V7CanonicalQM31

/-! Keep the four-way option assembly independent of packed-byte reduction.
This makes the literal-order certificate a small propositional proof instead
of asking the kernel to normalize four 31-bit finite sums at once. -/
def assembleC2Entry
    (a b c d : Option CanonicalM31) : Option CanonicalQM31 :=
  match a with
  | none => none
  | some a =>
      match b with
      | none => none
      | some b =>
          match c with
          | none => none
          | some c =>
              match d with
              | none => none
              | some d => some ⟨a, b, c, d⟩

def decodeC2Entry (value : C2Value) (helper : Fin 3)
    (slot : Fin 4) : Option CanonicalQM31 :=
  assembleC2Entry
    (decodeC2PackedLimb value (c2LimbIndex helper slot 0))
    (decodeC2PackedLimb value (c2LimbIndex helper slot 1))
    (decodeC2PackedLimb value (c2LimbIndex helper slot 2))
    (decodeC2PackedLimb value (c2LimbIndex helper slot 3))

theorem assembleC2Entry_of_eq_some
    (oa ob oc od : Option CanonicalM31) (a b c d : CanonicalM31)
    (ha : oa = some a) (hb : ob = some b)
    (hc : oc = some c) (hd : od = some d) :
    assembleC2Entry oa ob oc od = some ⟨a, b, c, d⟩ := by
  subst oa
  subst ob
  subst oc
  subst od
  rfl

end AspisPool.V7PackedC2Entry
