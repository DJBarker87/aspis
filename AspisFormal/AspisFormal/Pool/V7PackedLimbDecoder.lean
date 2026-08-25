import AspisFormal.Pool.V7MerkleQueryGrammar

/-!
# Exact Tag-73 packed-limb decoder

This memory-small K1.3 leaf decodes the deployed contiguous little-endian
31-bit packing into canonical integers. It intentionally does not import the
large QM31 field tower; the structural fibre layout and exact tower conversion
are separate kernel modules.
-/

set_option autoImplicit false

namespace AspisPool.V7PackedLimbDecoder

open AspisPool.V7MerkleQueryGrammar

def m31Modulus : Nat := 2147483647
abbrev CanonicalM31 := Fin m31Modulus

def c1LimbCount : Nat := 4 * 26
def c2LimbCount : Nat := 3 * 4 * 4

theorem exact_packed_geometry :
    c1LimbCount = 104 ∧
      c2LimbCount = 48 ∧
      c1LimbCount * 31 = 403 * 8 ∧
      c2LimbCount * 31 = 186 * 8 := by
  norm_num [c1LimbCount, c2LimbCount]

/-- One little-endian bit of a C1 packed limb. -/
def c1PackedBit (value : C1Value) (limb : Fin 104) (bit : Fin 31) : Nat :=
  let absolute := limb.val * 31 + bit.val
  let byteIndex : Fin 403 := ⟨absolute / 8, by
    have hlimb := limb.isLt
    have hbit := bit.isLt
    omega⟩
  ((value byteIndex).val / 2 ^ (absolute % 8)) % 2

/-- One little-endian bit of a C2 packed limb. -/
def c2PackedBit (value : C2Value) (limb : Fin 48) (bit : Fin 31) : Nat :=
  let absolute := limb.val * 31 + bit.val
  let byteIndex : Fin 186 := ⟨absolute / 8, by
    have hlimb := limb.isLt
    have hbit := bit.isLt
    omega⟩
  ((value byteIndex).val / 2 ^ (absolute % 8)) % 2

def c1PackedLimbNat (value : C1Value) (limb : Fin 104) : Nat :=
  ∑ bit : Fin 31, c1PackedBit value limb bit * 2 ^ bit.val

def c2PackedLimbNat (value : C2Value) (limb : Fin 48) : Nat :=
  ∑ bit : Fin 31, c2PackedBit value limb bit * 2 ^ bit.val

/-- Production accepts all 31-bit strings except the single value `P`.
Successful decoding retains the exact canonical integer and its bound. -/
def decodeC1PackedLimb (value : C1Value) (limb : Fin 104) : Option CanonicalM31 :=
  let raw := c1PackedLimbNat value limb
  if canonical : raw < m31Modulus then some ⟨raw, canonical⟩ else none

def decodeC2PackedLimb (value : C2Value) (limb : Fin 48) : Option CanonicalM31 :=
  let raw := c2PackedLimbNat value limb
  if canonical : raw < m31Modulus then some ⟨raw, canonical⟩ else none

theorem decoded_c1_limb_is_canonical
    (value : C1Value) (limb : Fin 104) (decoded : CanonicalM31)
    (_success : decodeC1PackedLimb value limb = some decoded) :
    decoded.val < 2147483647 := by
  exact decoded.isLt

theorem decoded_c2_limb_is_canonical
    (value : C2Value) (limb : Fin 48) (decoded : CanonicalM31)
    (_success : decodeC2PackedLimb value limb = some decoded) :
    decoded.val < 2147483647 := by
  exact decoded.isLt

#print axioms exact_packed_geometry
#print axioms decoded_c1_limb_is_canonical
#print axioms decoded_c2_limb_is_canonical

end AspisPool.V7PackedLimbDecoder
