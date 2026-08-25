import AspisFormal.V7CompactOneFold

/-!
# V7 complete-C2 authentication and 208-bit digest boundary

The selected V7 wire sends all three C2 lanes at all four fibre positions.
There is no inferred D value and therefore no reconstruction premise in the
accepted path.  This module proves that equality of the disclosed C2 view
fixes the complete fibre and hence its gamma-combined query value.

The 26-byte Merkle digest is modeled as deterministic truncation of a
32-byte hash output.  Collision resistance of that truncated function remains
an explicit cryptographic interface, with the generic classical parameter
checked separately as 104 bits.
-/

set_option autoImplicit false

namespace AspisV7AuthenticatedWire

inductive C2Lane
  | h
  | g
  | d
  deriving DecidableEq, Fintype

structure C2Fibre (K : Type*) where
  h : Fin 4 → K
  g : Fin 4 → K
  d : Fin 4 → K

def discloseC2 {K : Type*} (fibre : C2Fibre K) :
    C2Lane → Fin 4 → K
  | .h => fibre.h
  | .g => fibre.g
  | .d => fibre.d

theorem discloseC2_complete {K : Type*}
    (left right : C2Fibre K)
    (equalDisclosure : discloseC2 left = discloseC2 right) :
    left = right := by
  cases left with
  | mk leftH leftG leftD =>
    cases right with
    | mk rightH rightG rightD =>
      have hH := congrFun equalDisclosure C2Lane.h
      have hG := congrFun equalDisclosure C2Lane.g
      have hD := congrFun equalDisclosure C2Lane.d
      change leftH = rightH at hH
      change leftG = rightG at hG
      change leftD = rightD at hD
      subst rightH
      subst rightG
      subst rightD
      rfl

variable {K : Type*} [Field K]

def gammaCombinedFibre
    (gamma : K) (c1 : Fin 26 → Fin 4 → K) (c2 : C2Fibre K)
    (position : Fin 4) : K :=
  (∑ lane : Fin 26, gamma ^ lane.val * c1 lane position) +
    gamma ^ 26 * c2.h position +
    gamma ^ 27 * c2.g position +
    gamma ^ 28 * c2.d position

/-- Authenticating the complete disclosed C2 fibre authenticates every C2
term consumed by the unchanged V6 width-29 gamma combination. -/
theorem complete_c2_authenticates_gamma_combination
    (gamma : K) (c1 : Fin 26 → Fin 4 → K)
    (left right : C2Fibre K)
    (equalDisclosure : discloseC2 left = discloseC2 right) :
    gammaCombinedFibre gamma c1 left = gammaCombinedFibre gamma c1 right := by
  rw [discloseC2_complete left right equalDisclosure]

def truncateDigest {Byte : Type*} (digest : Fin 32 → Byte) : Fin 26 → Byte :=
  fun index => digest ⟨index.val, by omega⟩

theorem truncateDigest_deterministic {Byte : Type*}
    (left right : Fin 32 → Byte) (equalFullDigest : left = right) :
    truncateDigest left = truncateDigest right := by
  rw [equalFullDigest]

def TruncatedCollision {Input Byte : Type*}
    (hash : Input → Fin 32 → Byte) (left right : Input) : Prop :=
  left ≠ right ∧ truncateDigest (hash left) = truncateDigest (hash right)

/-- Named cryptographic boundary used by the complete V7 theorem.  The source
proof establishes the deterministic 26-byte truncation; this predicate is the
remaining collision-resistance assumption about the instantiated hash. -/
structure TruncatedHashBinding {Input Byte : Type*}
    (hash : Input → Fin 32 → Byte) : Prop where
  noAcceptedCollision : ∀ left right, ¬ TruncatedCollision hash left right

theorem digest_width_and_generic_collision_level :
    AspisV7CompactOneFold.digestBits = 208 ∧
      AspisV7CompactOneFold.classicalCollisionBits = 104 := by
  exact ⟨AspisV7CompactOneFold.digest_bits_eq,
    AspisV7CompactOneFold.classical_collision_bits_eq⟩

#print axioms discloseC2_complete
#print axioms complete_c2_authenticates_gamma_combination
#print axioms truncateDigest_deterministic
#print axioms digest_width_and_generic_collision_level

end AspisV7AuthenticatedWire
