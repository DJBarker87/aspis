import AspisFormal.K1.V7Tag73DeterministicRefinement

/-!
# Disjoint deployed Tag-73 transcript and typed-Merkle SHA grammars

Tag-73 uses one SHA-256 primitive for the Fiat--Shamir transcript and for the
two truncated 208-bit Merkle trees.  The compiler may account for those two
families separately only after proving that a Merkle call cannot pre-populate
an input later used by the transcript machine.

This leaf models the three byte-exact Merkle preimages used by
`v7_onefold.rs`/`v7_merkle208.rs`:

* `0x10 || 0x71 || c1[403] || salt[32]`;
* `0x10 || 0xf1 || c2[186] || salt[32]`; and
* `0x11 || left[26] || right[26]`.

Their lengths are respectively 437, 220 and 53 bytes.  Every deployed
transcript, squeeze, grinding and public-root-salt input has a different
length.  Thus the grammars are disjoint without pretending that the C1 and C2
internal-node domains are distinct: both trees intentionally use the same
`0x11` parent grammar, while their private leaves have distinct tags.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SharedShaGrammar

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement

/-! ## Exact typed-Merkle preimages -/

def typedMerkleLeafDomain : UInt8 := 0x10

def typedMerkleParentDomain : UInt8 := 0x11

def deployedC1LeafValueBytes : Nat := 403

def deployedC2LeafValueBytes : Nat := 186

inductive TypedMerklePreimage where
  | c1Leaf (value : Bytes deployedC1LeafValueBytes) (salt : Digest256)
  | c2Leaf (value : Bytes deployedC2LeafValueBytes) (salt : Digest256)
  | parent (left right : Digest208)

def TypedMerklePreimage.input : TypedMerklePreimage → ByteString
  | .c1Leaf value salt =>
      [typedMerkleLeafDomain, c1TreeTag] ++ bytes value ++ bytes salt
  | .c2Leaf value salt =>
      [typedMerkleLeafDomain, c2TreeTag] ++ bytes value ++ bytes salt
  | .parent left right =>
      [typedMerkleParentDomain] ++ bytes left ++ bytes right

@[simp] theorem typed_merkle_c1_leaf_input_length
    (value : Bytes deployedC1LeafValueBytes) (salt : Digest256) :
    (TypedMerklePreimage.c1Leaf value salt).input.length = 437 := by
  simp [TypedMerklePreimage.input, deployedC1LeafValueBytes]

@[simp] theorem typed_merkle_c2_leaf_input_length
    (value : Bytes deployedC2LeafValueBytes) (salt : Digest256) :
    (TypedMerklePreimage.c2Leaf value salt).input.length = 220 := by
  simp [TypedMerklePreimage.input, deployedC2LeafValueBytes]

@[simp] theorem typed_merkle_parent_input_length
    (left right : Digest208) :
    (TypedMerklePreimage.parent left right).input.length = 53 := by
  simp [TypedMerklePreimage.input]

theorem typed_merkle_preimage_length_cases (input : TypedMerklePreimage) :
    input.input.length = 437 ∨ input.input.length = 220 ∨
      input.input.length = 53 := by
  cases input <;> simp

/-! ## Exhaustive deployed transcript lengths -/

/-- No deployed absorb payload has one of the three lengths that would make
`state[32] || 0x00 || label || payload` as long as a typed Merkle preimage. -/
theorem payload_data_length_avoids_typed_merkle_offsets (payload : Payload) :
    payload.data.length ≠ 403 ∧ payload.data.length ≠ 186 ∧
      payload.data.length ≠ 19 := by
  cases payload <;>
    simp [Payload.data, profileBinding, circleBasisBinding, deploymentBytes,
      hidingPrecommitBytes, maskLayoutFingerprintLe,
      spendLayoutFactorFingerprintLe, stateOnlyRegistry]

/-- Every SHA input represented by the exact raw Tag-73 transcript machine
has a length different from all three deployed typed-Merkle preimages. -/
theorem raw_query_input_length_avoids_typed_merkle
    (before : Digest256) (role : RawQueryRole) :
    (role.input before).length ≠ 437 ∧
      (role.input before).length ≠ 220 ∧
      (role.input before).length ≠ 53 := by
  cases role with
  | absorb payload =>
      have avoided := payload_data_length_avoids_typed_merkle_offsets payload
      simp only [RawQueryRole.input, List.length_append, List.length_cons,
        List.length_nil, bytes_length]
      omega
  | squeezeOutput owner block =>
      simp [RawQueryRole.input]
  | squeezeAdvance owner block =>
      simp [RawQueryRole.input]
  | grind stage nonce =>
      simp [RawQueryRole.input]
  | publicRootSalt context treeTag =>
      rw [RawQueryRole.input, root_salt_input_length]
      norm_num

/-- The single deployed SHA table may therefore be split into transcript and
typed-Merkle restrictions without any input appearing in both restrictions. -/
theorem transcript_input_ne_typed_merkle_input
    (before : Digest256) (role : RawQueryRole)
    (merkle : TypedMerklePreimage) :
    role.input before ≠ merkle.input := by
  intro equalInputs
  have equalLengths := congrArg List.length equalInputs
  have avoided := raw_query_input_length_avoids_typed_merkle before role
  rcases avoided with ⟨not437, not220, not53⟩
  rcases typed_merkle_preimage_length_cases merkle with
    merkle437 | merkle220 | merkle53
  · exact not437 (equalLengths.trans merkle437)
  · exact not220 (equalLengths.trans merkle220)
  · exact not53 (equalLengths.trans merkle53)

/-- The two deployed private-leaf domains are distinct even before hashing.
Their widths already differ; the second byte also carries the distinct tree
tags `0x71` and `0xf1`. -/
theorem c1_leaf_input_ne_c2_leaf_input
    (c1 : Bytes deployedC1LeafValueBytes)
    (c2 : Bytes deployedC2LeafValueBytes) (salt1 salt2 : Digest256) :
    (TypedMerklePreimage.c1Leaf c1 salt1).input ≠
      (TypedMerklePreimage.c2Leaf c2 salt2).input := by
  intro equalInputs
  have equalLengths := congrArg List.length equalInputs
  simp at equalLengths

#print axioms typed_merkle_preimage_length_cases
#print axioms payload_data_length_avoids_typed_merkle_offsets
#print axioms raw_query_input_length_avoids_typed_merkle
#print axioms transcript_input_ne_typed_merkle_input
#print axioms c1_leaf_input_ne_c2_leaf_input

end AspisK1.V7Tag73SharedShaGrammar
