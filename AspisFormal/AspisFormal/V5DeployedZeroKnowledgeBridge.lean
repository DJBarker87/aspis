import AspisFormal.V5ConditionalHidingCapstoneV3
import AspisFormal.V5ComponentCBlockSamplerDirectHiding
import AspisFormal.V5ComponentCExactTowerDeployment
import AspisFormal.V5CryptographicAssumptions
import AspisFormal.V5RepairedRuntimeWireClassification
import AspisFormal.V5SaltedMerkleSimulator
import AspisFormal.V5SelectionHidingAbort

/-!
# What is needed to carry the V5 hiding proof to the deployed view

The finite algebra in this repository proves a strong statement about a
modeled view: after ideal uniform masks are sampled, the joint Component A,
H-copy, Component B, and Component C values have the same distribution for
two compatible private witnesses.  That theorem is
`conditional_complete_joint_hiding_v3`.

This file records the larger public view of the released execution and keeps
the steps from that mathematical law to deployed bytes separate.  The final
theorem is deliberately conditional.  It does not claim that SHA-256,
Poseidon2, the Rust implementation, the Fiat--Shamir compiler, or the archived
mainnet bytes have already been connected to the mathematical experiment.

There are two useful conclusions here:

* the mathematical hiding theorem remains true after any deterministic
  encoding of the algebraic output that theorem actually contains;
* if each named implementation or cryptographic hybrid is supplied, the
  statistical distance between two deployed views is at most the sum of the
  supplied errors on the two sides.

The repaired byte inventory assigns every byte of the current 75,358-byte
proof body exactly one semantic class.  Discharging those classes still
requires the separately named production and cryptographic results.  A small
counterexample also shows that equality of mathematical laws says nothing
about unrelated deployed laws without a code-to-model bridge.
-/

open scoped ENNReal

namespace AspisV5DeployedZeroKnowledgeBridge

open AspisFormal.V5ExactRuntimeWireRepair
open AspisFormal.V5RepairedRuntimeWireClassification
open AspisV5ConditionalHidingCapstoneV3
open AspisV5ComponentCBlockSamplerDirectHiding
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCDirectHiding
open AspisV5ComponentCExactTowerDeployment
open AspisV5ComponentCPreCProjection
open AspisV5ComponentCPreCProjectionMixed
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCStoppingTimeSampler
open AspisV5ComponentCUnconditionedComposition
open AspisV5MixedFieldComposition
open AspisV5SaltedMerkleSimulator
open AspisV5TranscriptConnection

/-! ## The released public byte view -/

/-
These wrapper constants and offsets are the current production layout from
`v5_full_transaction.rs::parse_v5_full_cu_public_inputs` and
`lifecycle.rs::uploaded_proof_bounds`.  They are repeated here instead of
importing `V5FreezeCompleteWireView`: that older module deliberately models
the retired 27,200-byte diagnostic prefix and must not be a dependency of the
75,358-byte released-proof argument.
-/

def releasedInstructionBytes : Nat := 169
def sealedProofAccountHeaderBytes : Nat := 40

inductive ReleasedInstructionField where
  | tag
  | currentAnchor
  | nullifier
  | outputCommitment
  | outputAnchor
  | assetId
  | fee
  | deploymentDomain
  deriving DecidableEq, Fintype

def ReleasedInstructionField.start : ReleasedInstructionField → Nat
  | .tag => 0
  | .currentAnchor => 1
  | .nullifier => 33
  | .outputCommitment => 65
  | .outputAnchor => 97
  | .assetId => 129
  | .fee => 133
  | .deploymentDomain => 137

def ReleasedInstructionField.bytes : ReleasedInstructionField → Nat
  | .tag => 1
  | .currentAnchor | .nullifier | .outputCommitment | .outputAnchor => 32
  | .assetId | .fee => 4
  | .deploymentDomain => 32

def ReleasedInstructionField.stop (field : ReleasedInstructionField) : Nat :=
  field.start + field.bytes

def releasedInstructionFieldAt (offset : Fin releasedInstructionBytes) :
    ReleasedInstructionField :=
  if offset.val < 1 then .tag
  else if offset.val < 33 then .currentAnchor
  else if offset.val < 65 then .nullifier
  else if offset.val < 97 then .outputCommitment
  else if offset.val < 129 then .outputAnchor
  else if offset.val < 133 then .assetId
  else if offset.val < 137 then .fee
  else .deploymentDomain

theorem released_instruction_layout_is_exact :
    ReleasedInstructionField.start .tag = 0 ∧
      ReleasedInstructionField.stop .tag =
        ReleasedInstructionField.start .currentAnchor ∧
      ReleasedInstructionField.stop .currentAnchor =
        ReleasedInstructionField.start .nullifier ∧
      ReleasedInstructionField.stop .nullifier =
        ReleasedInstructionField.start .outputCommitment ∧
      ReleasedInstructionField.stop .outputCommitment =
        ReleasedInstructionField.start .outputAnchor ∧
      ReleasedInstructionField.stop .outputAnchor =
        ReleasedInstructionField.start .assetId ∧
      ReleasedInstructionField.stop .assetId =
        ReleasedInstructionField.start .fee ∧
      ReleasedInstructionField.stop .fee =
        ReleasedInstructionField.start .deploymentDomain ∧
      ReleasedInstructionField.stop .deploymentDomain = releasedInstructionBytes := by
  decide

theorem released_instruction_field_at_contains
    (offset : Fin releasedInstructionBytes) :
    (releasedInstructionFieldAt offset).start ≤ offset.val ∧
      offset.val < (releasedInstructionFieldAt offset).stop := by
  unfold releasedInstructionFieldAt
  split_ifs <;>
    simp_all [ReleasedInstructionField.start, ReleasedInstructionField.stop,
      ReleasedInstructionField.bytes, releasedInstructionBytes]
  all_goals omega

theorem released_instruction_fields_pairwise_disjoint :
    ∀ first second : ReleasedInstructionField, first ≠ second →
      first.stop ≤ second.start ∨ second.stop ≤ first.start := by
  decide

theorem every_instruction_offset_has_exactly_one_field
    (offset : Fin releasedInstructionBytes) :
    ∃! field : ReleasedInstructionField,
      field.start ≤ offset.val ∧ offset.val < field.stop := by
  refine ⟨releasedInstructionFieldAt offset,
    released_instruction_field_at_contains offset, ?_⟩
  intro field hfield
  by_contra hne
  have hdisjoint := released_instruction_fields_pairwise_disjoint
    field (releasedInstructionFieldAt offset) hne
  have hselected := released_instruction_field_at_contains offset
  omega

inductive SealedProofHeaderField where
  | magic
  | proofLength
  | zeroUploadAuthority
  deriving DecidableEq, Fintype

def SealedProofHeaderField.start : SealedProofHeaderField → Nat
  | .magic => 0
  | .proofLength => 4
  | .zeroUploadAuthority => 8

def SealedProofHeaderField.bytes : SealedProofHeaderField → Nat
  | .magic => 4
  | .proofLength => 4
  | .zeroUploadAuthority => 32

def SealedProofHeaderField.stop (field : SealedProofHeaderField) : Nat :=
  field.start + field.bytes

def sealedProofHeaderFieldAt (offset : Fin sealedProofAccountHeaderBytes) :
    SealedProofHeaderField :=
  if offset.val < 4 then .magic
  else if offset.val < 8 then .proofLength
  else .zeroUploadAuthority

theorem sealed_proof_header_layout_is_exact :
    SealedProofHeaderField.start .magic = 0 ∧
      SealedProofHeaderField.stop .magic =
        SealedProofHeaderField.start .proofLength ∧
      SealedProofHeaderField.stop .proofLength =
        SealedProofHeaderField.start .zeroUploadAuthority ∧
      SealedProofHeaderField.stop .zeroUploadAuthority =
        sealedProofAccountHeaderBytes := by
  decide

theorem sealed_proof_header_field_at_contains
    (offset : Fin sealedProofAccountHeaderBytes) :
    (sealedProofHeaderFieldAt offset).start ≤ offset.val ∧
      offset.val < (sealedProofHeaderFieldAt offset).stop := by
  unfold sealedProofHeaderFieldAt
  split_ifs <;>
    simp_all [SealedProofHeaderField.start, SealedProofHeaderField.stop,
      SealedProofHeaderField.bytes, sealedProofAccountHeaderBytes]

theorem sealed_proof_header_fields_pairwise_disjoint :
    ∀ first second : SealedProofHeaderField, first ≠ second →
      first.stop ≤ second.start ∨ second.stop ≤ first.start := by
  decide

theorem every_sealed_header_offset_has_exactly_one_field
    (offset : Fin sealedProofAccountHeaderBytes) :
    ∃! field : SealedProofHeaderField,
      field.start ≤ offset.val ∧ offset.val < field.stop := by
  refine ⟨sealedProofHeaderFieldAt offset,
    sealed_proof_header_field_at_contains offset, ?_⟩
  intro field hfield
  by_contra hne
  have hdisjoint := sealed_proof_header_fields_pairwise_disjoint
    field (sealedProofHeaderFieldAt offset) hne
  have hselected := sealed_proof_header_field_at_contains offset
  omega

/-- One coordinate of the released byte vector, separated into the current
instruction, the sealed proof-account header, or the repaired proof body. -/
abbrev ReleasedByteCoordinate :=
  Sum (Fin releasedInstructionBytes)
    (Sum (Fin sealedProofAccountHeaderBytes)
      (RuntimeBodyByte currentFixtureRuntimeShape))

def releasedByteOffset : ReleasedByteCoordinate → Nat
  | .inl instruction => instruction.val
  | .inr (.inl header) => releasedInstructionBytes + header.val
  | .inr (.inr proof) =>
      releasedInstructionBytes + sealedProofAccountHeaderBytes + proof.val

/-- Public chain data which is visible in addition to the instruction and
proof-account bytes.  Addresses are their 32-byte binary encodings and the
transaction signature is its 64-byte encoding.  `archivedProgramDigest` is
needed because the upgradeable ProgramData account was closed after the
demonstration. -/
structure ArchivedChainContext where
  programId : FixedBytes 32
  archivedProgramDigest : FixedBytes 32
  transactionSignature : FixedBytes 64
  slot : Nat
  accountKeys : List (FixedBytes 32)
  computeUnits : Nat

/-- Instruction, sealed account header, and repaired proof body bytes in the
archived release. -/
def currentCompleteReleasedBytes : Nat :=
  releasedInstructionBytes + sealedProofAccountHeaderBytes +
    currentFixtureRepairedProofBytes

theorem released_byte_offset_lt (coordinate : ReleasedByteCoordinate) :
    releasedByteOffset coordinate < currentCompleteReleasedBytes := by
  rcases coordinate with instruction | headerOrProof
  · change instruction.val < currentCompleteReleasedBytes
    exact instruction.isLt.trans_le (by
      simp only [currentCompleteReleasedBytes]
      omega)
  · rcases headerOrProof with header | proof
    · change releasedInstructionBytes + header.val < currentCompleteReleasedBytes
      exact (Nat.add_lt_add_left header.isLt releasedInstructionBytes).trans_le (by
        simp [currentCompleteReleasedBytes])
    · have hproof := proof.isLt
      simp only [releasedByteOffset, currentCompleteReleasedBytes,
        releasedInstructionBytes, sealedProofAccountHeaderBytes,
        currentFixtureRepairedProofBytes] at hproof ⊢
      omega

def releasedByteFin (coordinate : ReleasedByteCoordinate) :
    Fin currentCompleteReleasedBytes :=
  ⟨releasedByteOffset coordinate, released_byte_offset_lt coordinate⟩

theorem releasedByteFin_injective : Function.Injective releasedByteFin := by
  intro left right equal
  have equalValue := congrArg Fin.val equal
  rcases left with leftInstruction | leftHeaderOrProof
  · rcases right with rightInstruction | rightHeaderOrProof
    · apply congrArg Sum.inl
      apply Fin.ext
      simpa [releasedByteFin, releasedByteOffset] using equalValue
    · rcases rightHeaderOrProof with rightHeader | rightProof
      · have hleft := leftInstruction.isLt
        change leftInstruction.val =
          releasedInstructionBytes + rightHeader.val at equalValue
        norm_num [releasedInstructionBytes] at hleft equalValue
        omega
      · have hleft := leftInstruction.isLt
        change leftInstruction.val = releasedInstructionBytes +
          sealedProofAccountHeaderBytes + rightProof.val at equalValue
        norm_num [releasedInstructionBytes, sealedProofAccountHeaderBytes]
          at hleft equalValue
        omega
  · rcases leftHeaderOrProof with leftHeader | leftProof
    · rcases right with rightInstruction | rightHeaderOrProof
      · have hright := rightInstruction.isLt
        change releasedInstructionBytes + leftHeader.val =
          rightInstruction.val at equalValue
        norm_num [releasedInstructionBytes] at hright equalValue
        omega
      · rcases rightHeaderOrProof with rightHeader | rightProof
        · apply congrArg (fun value => Sum.inr (Sum.inl value))
          apply Fin.ext
          change releasedInstructionBytes + leftHeader.val =
            releasedInstructionBytes + rightHeader.val at equalValue
          omega
        · have hleft := leftHeader.isLt
          change releasedInstructionBytes + leftHeader.val =
            releasedInstructionBytes + sealedProofAccountHeaderBytes +
              rightProof.val at equalValue
          norm_num [sealedProofAccountHeaderBytes] at hleft equalValue
          omega
    · rcases right with rightInstruction | rightHeaderOrProof
      · have hright := rightInstruction.isLt
        change releasedInstructionBytes + sealedProofAccountHeaderBytes +
          leftProof.val = rightInstruction.val at equalValue
        norm_num [releasedInstructionBytes, sealedProofAccountHeaderBytes]
          at hright equalValue
        omega
      · rcases rightHeaderOrProof with rightHeader | rightProof
        · have hright := rightHeader.isLt
          change releasedInstructionBytes + sealedProofAccountHeaderBytes +
            leftProof.val = releasedInstructionBytes + rightHeader.val at equalValue
          norm_num [sealedProofAccountHeaderBytes] at hright equalValue
          omega
        · apply congrArg (fun value => Sum.inr (Sum.inr value))
          apply Fin.ext
          change releasedInstructionBytes + sealedProofAccountHeaderBytes +
            leftProof.val = releasedInstructionBytes +
              sealedProofAccountHeaderBytes + rightProof.val at equalValue
          omega

theorem releasedByteFin_surjective : Function.Surjective releasedByteFin := by
  intro offset
  by_cases hinstruction : offset.val < releasedInstructionBytes
  · refine ⟨Sum.inl ⟨offset.val, hinstruction⟩, ?_⟩
    apply Fin.ext
    rfl
  · by_cases hheader :
        offset.val < releasedInstructionBytes + sealedProofAccountHeaderBytes
    · have hlocal : offset.val - releasedInstructionBytes <
          sealedProofAccountHeaderBytes := by omega
      refine ⟨Sum.inr (Sum.inl ⟨offset.val - releasedInstructionBytes,
        hlocal⟩), ?_⟩
      apply Fin.ext
      simp only [releasedByteFin, releasedByteOffset]
      omega
    · have hlocal :
          offset.val - (releasedInstructionBytes + sealedProofAccountHeaderBytes) <
            currentFixtureRepairedProofBytes := by
        have hoffset := offset.isLt
        simp only [currentCompleteReleasedBytes] at hoffset
        omega
      refine ⟨Sum.inr (Sum.inr
        ⟨offset.val - (releasedInstructionBytes + sealedProofAccountHeaderBytes),
          hlocal⟩), ?_⟩
      apply Fin.ext
      simp only [releasedByteFin, releasedByteOffset]
      omega

/-- The three source-level regions are neither overlapping nor incomplete:
their coordinates are in bijection with every byte of the released vector. -/
noncomputable def releasedByteCoordinateEquiv :
    ReleasedByteCoordinate ≃ Fin currentCompleteReleasedBytes :=
  Equiv.ofBijective releasedByteFin
    ⟨releasedByteFin_injective, releasedByteFin_surjective⟩

inductive ReleasedByteClass where
  | instruction (field : ReleasedInstructionField)
  | sealedHeader (field : SealedProofHeaderField)
  | proofBody (classification : CoverageClass)
  deriving DecidableEq

def releasedByteClass : ReleasedByteCoordinate → ReleasedByteClass
  | .inl instruction => .instruction (releasedInstructionFieldAt instruction)
  | .inr (.inl header) => .sealedHeader (sealedProofHeaderFieldAt header)
  | .inr (.inr proof) => .proofBody (runtimeBodyByteClass proof)

def ReleasedClassifiedAs (coordinate : ReleasedByteCoordinate)
    (classification : ReleasedByteClass) : Prop :=
  releasedByteClass coordinate = classification

/-- Every one of the 75,567 released bytes has one and only one class.  The
instruction fields are public inputs shared by the two witnesses in a
zero-knowledge comparison; that equality is a premise, not a consequence of
the hiding theorem. -/
theorem every_released_byte_has_exactly_one_class
    (coordinate : ReleasedByteCoordinate) :
  ∃! classification, ReleasedClassifiedAs coordinate classification :=
  ⟨releasedByteClass coordinate, rfl,
    fun _classification hclassification => hclassification.symm⟩

noncomputable def releasedVectorByteClass
    (offset : Fin currentCompleteReleasedBytes) : ReleasedByteClass :=
  releasedByteClass (releasedByteCoordinateEquiv.symm offset)

/-- Absolute-offset form of the total inventory used by
`DeployedPublicView.releasedBytes`. -/
theorem every_released_vector_offset_has_exactly_one_class
    (offset : Fin currentCompleteReleasedBytes) :
    ∃! classification, releasedVectorByteClass offset = classification :=
  ⟨releasedVectorByteClass offset, rfl,
    fun _classification hclassification => hclassification.symm⟩

theorem released_coordinate_count_is_75567 :
    Fintype.card ReleasedByteCoordinate = 75567 := by
  rw [Fintype.card_congr releasedByteCoordinateEquiv, Fintype.card_fin]
  norm_num [currentCompleteReleasedBytes, releasedInstructionBytes,
    sealedProofAccountHeaderBytes, current_fixture_repaired_proof_is_75358]

theorem released_region_boundaries_are_exact :
    releasedInstructionBytes = 169 ∧
      releasedInstructionBytes + sealedProofAccountHeaderBytes = 209 ∧
      currentCompleteReleasedBytes = 75567 := by
  exact ⟨rfl, rfl, by
    norm_num [currentCompleteReleasedBytes, releasedInstructionBytes,
      sealedProofAccountHeaderBytes, current_fixture_repaired_proof_is_75358]⟩

/-- The released spend view modeled in this file.

The byte vector contains the 169-byte instruction, 40-byte sealed-account
header, and exact 75,358-byte repaired proof body.  Storing one vector rather
than selected parsed fields makes padding, selector, roots, salts, nonces, and
frontier bytes part of the view rather than silently dropping them.

This is not every observable item in Solana history.  Full transaction
messages, upload timing, balances, logs, account data outside this spend, and
the rest of the archived lifecycle are not fields of this structure.  A
deployed zero-knowledge claim for those observations needs an additional
public-context/release argument; the name of this structure must not be read
as proving that argument. -/
structure DeployedPublicView where
  chain : ArchivedChainContext
  releasedBytes : Fin currentCompleteReleasedBytes → Byte

abbrev ReleasedInstructionBytes := Fin releasedInstructionBytes → Byte
abbrev SealedProofHeaderBytes := Fin sealedProofAccountHeaderBytes → Byte
abbrev ReleasedProofBodyBytes :=
  RuntimeBodyByte currentFixtureRuntimeShape → Byte

/-- The three byte arrays before concatenation.  Keeping them separate makes
the boundary clear: the instruction is the public statement, the sealed
header is lifecycle metadata, and only the last array is the proof body. -/
@[ext] structure ReleasedByteParts where
  instruction : ReleasedInstructionBytes
  sealedHeader : SealedProofHeaderBytes
  proofBody : ReleasedProofBodyBytes

/-- Concatenate the three exact current-release arrays. -/
noncomputable def encodeReleasedByteParts (parts : ReleasedByteParts) :
    Fin currentCompleteReleasedBytes → Byte :=
  fun offset =>
    match releasedByteCoordinateEquiv.symm offset with
    | .inl instruction => parts.instruction instruction
    | .inr (.inl header) => parts.sealedHeader header
    | .inr (.inr proof) => parts.proofBody proof

/-- Split a released vector at offsets 169 and 209. -/
def decodeReleasedByteParts
    (bytes : Fin currentCompleteReleasedBytes → Byte) : ReleasedByteParts where
  instruction instruction := bytes (releasedByteFin (.inl instruction))
  sealedHeader header := bytes (releasedByteFin (.inr (.inl header)))
  proofBody proof := bytes (releasedByteFin (.inr (.inr proof)))

theorem decode_encode_released_byte_parts (parts : ReleasedByteParts) :
    decodeReleasedByteParts (encodeReleasedByteParts parts) = parts := by
  cases parts with
  | mk instruction sealedHeader proofBody =>
      apply ReleasedByteParts.ext <;> funext offset <;>
        simp [decodeReleasedByteParts, encodeReleasedByteParts,
          releasedByteCoordinateEquiv]

theorem encode_decode_released_byte_parts
    (bytes : Fin currentCompleteReleasedBytes → Byte) :
    encodeReleasedByteParts (decodeReleasedByteParts bytes) = bytes := by
  funext offset
  generalize hcoordinate : releasedByteCoordinateEquiv.symm offset = coordinate
  have hfin : releasedByteFin coordinate = offset := by
    rw [← hcoordinate]
    exact releasedByteCoordinateEquiv.apply_symm_apply offset
  rcases coordinate with instruction | headerOrProof
  · simpa [encodeReleasedByteParts, decodeReleasedByteParts,
      hcoordinate] using congrArg bytes hfin
  · rcases headerOrProof with header | proof
    · simpa [encodeReleasedByteParts, decodeReleasedByteParts,
        hcoordinate] using congrArg bytes hfin
    · simpa [encodeReleasedByteParts, decodeReleasedByteParts,
        hcoordinate] using congrArg bytes hfin

/-- Exact lossless correspondence between the structured current wrapper and
the single 75,567-byte vector stored in `DeployedPublicView`. -/
noncomputable def releasedBytePartsEquiv :
    ReleasedByteParts ≃ (Fin currentCompleteReleasedBytes → Byte) where
  toFun := encodeReleasedByteParts
  invFun := decodeReleasedByteParts
  left_inv := decode_encode_released_byte_parts
  right_inv := encode_decode_released_byte_parts

noncomputable def assembleDeployedPublicView
    (chain : ArchivedChainContext) (parts : ReleasedByteParts) :
    DeployedPublicView :=
  ⟨chain, encodeReleasedByteParts parts⟩

/-- Once chain metadata, the public instruction, and the sealed header are
fixed equally on both sides, equality of proof-body laws lifts exactly to the
full modeled released-spend law.  This deterministic theorem adds no security
claim about how production Rust obtains those arrays. -/
theorem fixed_public_data_preserves_proof_body_hiding
    (chain : ArchivedChainContext)
    (instruction : ReleasedInstructionBytes)
    (sealedHeader : SealedProofHeaderBytes)
    (left right : PMF ReleasedProofBodyBytes)
    (hbody : left = right) :
    left.map (fun proofBody => assembleDeployedPublicView chain
        ⟨instruction, sealedHeader, proofBody⟩) =
      right.map (fun proofBody => assembleDeployedPublicView chain
        ⟨instruction, sealedHeader, proofBody⟩) := by
  rw [hbody]

/-- Direct composition with an algebraic hiding theorem: deterministic proof
encoding followed by the fixed public wrapper cannot distinguish two equal
model laws.  This theorem says nothing about whether `encodeProof` is the Rust
serializer; that is exactly the correspondence below. -/
theorem fixed_public_data_preserves_encoded_hiding {AlgebraicView : Type*}
    (chain : ArchivedChainContext)
    (instruction : ReleasedInstructionBytes)
    (sealedHeader : SealedProofHeaderBytes)
    (encodeProof : AlgebraicView → ReleasedProofBodyBytes)
    (left right : PMF AlgebraicView)
    (hmodel : left = right) :
    left.map (fun algebraic => assembleDeployedPublicView chain
        ⟨instruction, sealedHeader, encodeProof algebraic⟩) =
      right.map (fun algebraic => assembleDeployedPublicView chain
        ⟨instruction, sealedHeader, encodeProof algebraic⟩) := by
  rw [hmodel]

/-- The exact deterministic production obligation for release encoding.  It
states equality to the current 169 + 40 + 75,358 concatenation; it does not
smuggle in witness independence or a hash assumption. -/
def ExactReleasedEncodingCorrespondence {Model : Type*}
    (rustReleasedBytes : Model → Fin currentCompleteReleasedBytes → Byte)
    (instruction : Model → ReleasedInstructionBytes)
    (sealedHeader : Model → SealedProofHeaderBytes)
    (proofBody : Model → ReleasedProofBodyBytes) : Prop :=
  ∀ model, rustReleasedBytes model = encodeReleasedByteParts
    ⟨instruction model, sealedHeader model, proofBody model⟩

theorem released_encoding_law_of_exact_correspondence {Model : Type*}
    (law : PMF Model)
    (rustReleasedBytes : Model → Fin currentCompleteReleasedBytes → Byte)
    (instruction : Model → ReleasedInstructionBytes)
    (sealedHeader : Model → SealedProofHeaderBytes)
    (proofBody : Model → ReleasedProofBodyBytes)
    (hexact : ExactReleasedEncodingCorrespondence rustReleasedBytes
      instruction sealedHeader proofBody) :
    law.map rustReleasedBytes = law.map (fun model => encodeReleasedByteParts
      ⟨instruction model, sealedHeader model, proofBody model⟩) := by
  congr 1
  funext model
  exact hexact model

/-- The archived proof body has the repaired, current-source length. -/
theorem released_proof_body_byte_count :
    currentFixtureRepairedProofBytes = 75358 :=
  current_fixture_repaired_proof_is_75358

/-- Instruction, sealed header, and proof body contain 75,567 bytes in total. -/
theorem released_instruction_header_and_proof_byte_count :
    currentCompleteReleasedBytes = 75567 := by
  norm_num [currentCompleteReleasedBytes, releasedInstructionBytes,
    sealedProofAccountHeaderBytes, current_fixture_repaired_proof_is_75358]

/-- Every byte of the actual 75,358-byte proof body has exactly one class in
the repaired runtime inventory.  This is a total inventory, not a proof that
each cryptographic or implementation obligation attached to a class holds. -/
theorem every_released_proof_byte_has_exactly_one_class
    (coordinate : RuntimeBodyByte currentFixtureRuntimeShape) :
    ∃! classification, ClassifiedAs coordinate classification :=
  every_runtime_body_coordinate_has_exactly_one_class coordinate

/-- The current selector is byte 19,135 of the repaired proof body and is
classified as honest-selector metadata.  The obsolete 27,199 position came
from the retired layout and is not used here. -/
theorem released_selector_position_and_class_are_exact :
    fixedSemanticByteOffset querySelectorCoordinate = 19135 ∧
      fixedSemanticByteClass querySelectorCoordinate = .honestSelectorMetadata ∧
      ∀ shape, runtimeBodyByteClass (querySelectorRuntimeByte shape) =
        .honestSelectorMetadata :=
  query_selector_is_byte_19135_and_honest_metadata

/-! ## Individually named deployment steps -/

variable {View : Type*}

/-
The following bounds use statistical distance.  For `View =
DeployedPublicView` they concern every field of the modeled structure above,
not omitted lifecycle/RPC observations.  Ordinary computational hash
assumptions do not provide raw-byte statistical-distance bounds.  A
computational application must instead choose `View` to be an adversary's
observable output (or replace this metric with a proved
computational-indistinguishability relation) and justify each corresponding
advantage bound.  This file performs neither conversion silently.
-/

/-- Exact equality between the archived bytes and the bytes emitted by the
deployed runtime.  This includes transaction/account reconstruction after the
live accounts were closed. -/
def ArchiveMatchesDeployedRuntime (archived runtime : PMF View) : Prop :=
  archived = runtime

/-- Statistical loss introduced when the adaptive Fiat--Shamir compiler
replaces fixed-schedule experiments.  A computational compiler theorem cannot
be inserted here directly; it must first be stated for an adversary's output,
or this metric must be replaced.  No compiler theorem is asserted by this
definition. -/
def CompilerHybrid (runtime compiledModel : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist runtime compiledModel ≤ ε

/-- Loss at the remaining universal Rust-transcript-driver equality. -/
def RustTranscriptDriverHybrid (compiledModel sourceModel : PMF View)
    (ε : ℝ≥0∞) : Prop :=
  statDist compiledModel sourceModel ≤ ε

/-- Loss between the source-shaped transcript and the SHA-256 specification. -/
def SHA256ImplementationHybrid (sourceModel shaSpecification : PMF View)
    (ε : ℝ≥0∞) : Prop :=
  statDist sourceModel shaSpecification ≤ ε

/-- Explicit SHA-256 collision branch.  Digest width alone does not supply
this bound. -/
def SHA256CollisionHybrid (before after : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist before after ≤ ε

/-- Explicit SHA-256 preimage branch. -/
def SHA256PreimageHybrid (before after : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist before after ≤ ε

/-- Loss for replacing specified SHA-256 transcript behavior by the ideal
random-oracle experiment used by the Fiat--Shamir argument. -/
def SHA256RandomOracleHybrid (shaSpecification idealOracle : PMF View)
    (ε : ℝ≥0∞) : Prop :=
  statDist shaSpecification idealOracle ≤ ε

/-- Exact byte serialization/parser correspondence.  This is distinct from
cryptographic hiding: it says that the modeled fields are neither omitted nor
reordered in the accepted Rust byte stream. -/
def SerializationCorrespondence (transcriptModel serializedModel : PMF View) : Prop :=
  transcriptModel = serializedModel

/-- Loss for replacing the five salted Merkle commitments and openings by
their simulator.  Instantiating this premise for SHA-256 requires the
oracle-relative commitment analysis; the fixed-function
`SaltHidingHash` theorem alone does not supply it. -/
def CommitmentHybrid (serializedModel commitmentModel : PMF View)
    (ε : ℝ≥0∞) : Prop :=
  statDist serializedModel commitmentModel ≤ ε

/-- Loss between production Poseidon2 and its mathematical specification.
Known-answer tests alone do not establish a universal equality. -/
def Poseidon2ImplementationHybrid (before after : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist before after ≤ ε

/-- Explicit Poseidon2 collision branch. -/
def Poseidon2CollisionHybrid (before after : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist before after ≤ ε

/-- Explicit Poseidon2 preimage branch. -/
def Poseidon2PreimageHybrid (before after : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist before after ≤ ε

/-- Loss for replacing the finite-seed production entropy expander by its
ideal stream experiment. -/
def EntropyExpanderHybrid (before after : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist before after ≤ ε

/-- Loss at the production sampler/code boundary.  The ideal iid-u32
variable-consumption calculation, including first success and the 16-word
limit, is already exact in `V5ComponentCStoppingTimeSampler`.  This term is
only for connecting the finite-seed Rust stream and source operations to that
proved experiment. -/
def RejectionSamplerHybrid (before after : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist before after ≤ ε

/-- Loss for replacing the domain-separated joint source by the independent
product of the A/H/B and Component-C sources used in the mathematical proof. -/
def SourceIndependenceHybrid (before after : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist before after ≤ ε

/-- Loss at retry, least-good selection, and the public abort event.  The
existing cap-17 theorem makes this zero inside its modeled iid schedule law
once every good branch has the same law for the two witnesses.  Connecting
production entropy, fatal build failures, fixed-boundary release, and the Rust
manager to that law is still a separate correspondence obligation. -/
def RetrySelectionHybrid (before after : PMF View) (ε : ℝ≥0∞) : Prop :=
  statDist before after ≤ ε

/-- The exact Rust-to-Lean equality after all probabilistic hybrids: field
decoding, basis/index order, A/H/B maps, Component-C encoding and folds, and
the algebraic output represented by the maintained mathematical law agree.
Commitments, wrapper bytes, and other chain observations require their own
steps above and are not included merely by this definition. -/
def RustToMathematicalViewCorrespondence
    (algebraicModel mathematicalLaw : PMF View) : Prop :=
  algebraicModel = mathematicalLaw

/-- Every non-exact loss for one side of the deployed-view hybrid.  The names
match the primitive-failure ledger in `V5CryptographicAssumptions`, with the
additional compiler, salted-commitment, and entropy/selection steps needed by
the hiding argument. -/
structure SideError where
  compiler : ℝ≥0∞
  rustTranscriptDriver : ℝ≥0∞
  sha256Implementation : ℝ≥0∞
  sha256Collision : ℝ≥0∞
  sha256Preimage : ℝ≥0∞
  sha256RandomOracle : ℝ≥0∞
  commitment : ℝ≥0∞
  poseidon2Implementation : ℝ≥0∞
  poseidon2Collision : ℝ≥0∞
  poseidon2Preimage : ℝ≥0∞
  entropyExpander : ℝ≥0∞
  rejectionSampler : ℝ≥0∞
  sourceIndependence : ℝ≥0∞
  retrySelection : ℝ≥0∞

def SideError.total (ε : SideError) : ℝ≥0∞ :=
  ε.compiler + ε.rustTranscriptDriver + ε.sha256Implementation +
    ε.sha256Collision + ε.sha256Preimage + ε.sha256RandomOracle +
    ε.commitment + ε.poseidon2Implementation + ε.poseidon2Collision +
    ε.poseidon2Preimage + ε.entropyExpander + ε.rejectionSampler +
    ε.sourceIndependence + ε.retrySelection

/-- One side of the hybrid chain is within the sum of its explicitly
named error terms of the mathematical law. -/
theorem one_side_close_to_mathematical
    (archived runtime compiledModel sourceTranscript shaSpecification
      shaCollisionIdeal shaPreimageIdeal idealOracle serializedModel
      commitmentModel poseidonSpecification poseidonCollisionIdeal
      poseidonPreimageIdeal entropyIdeal samplerIdeal independentSourceIdeal
      algebraicModel mathematicalLaw : PMF View)
    (ε : SideError)
    (harchive : ArchiveMatchesDeployedRuntime archived runtime)
    (hcompiler : CompilerHybrid runtime compiledModel ε.compiler)
    (hrustTranscript : RustTranscriptDriverHybrid compiledModel sourceTranscript
      ε.rustTranscriptDriver)
    (hshaImplementation : SHA256ImplementationHybrid sourceTranscript
      shaSpecification ε.sha256Implementation)
    (hshaCollision : SHA256CollisionHybrid shaSpecification shaCollisionIdeal
      ε.sha256Collision)
    (hshaPreimage : SHA256PreimageHybrid shaCollisionIdeal shaPreimageIdeal
      ε.sha256Preimage)
    (hshaOracle : SHA256RandomOracleHybrid shaPreimageIdeal idealOracle
      ε.sha256RandomOracle)
    (hserialization : SerializationCorrespondence idealOracle serializedModel)
    (hcommitment : CommitmentHybrid serializedModel commitmentModel ε.commitment)
    (hposeidonImplementation : Poseidon2ImplementationHybrid commitmentModel
      poseidonSpecification ε.poseidon2Implementation)
    (hposeidonCollision : Poseidon2CollisionHybrid poseidonSpecification
      poseidonCollisionIdeal ε.poseidon2Collision)
    (hposeidonPreimage : Poseidon2PreimageHybrid poseidonCollisionIdeal
      poseidonPreimageIdeal ε.poseidon2Preimage)
    (hentropy : EntropyExpanderHybrid poseidonPreimageIdeal entropyIdeal
      ε.entropyExpander)
    (hsampler : RejectionSamplerHybrid entropyIdeal samplerIdeal
      ε.rejectionSampler)
    (hsource : SourceIndependenceHybrid samplerIdeal independentSourceIdeal
      ε.sourceIndependence)
    (hselection : RetrySelectionHybrid independentSourceIdeal algebraicModel
      ε.retrySelection)
    (hcode : RustToMathematicalViewCorrespondence algebraicModel mathematicalLaw) :
    statDist archived mathematicalLaw ≤ ε.total := by
  subst archived
  subst serializedModel
  subst algebraicModel
  calc
    statDist runtime mathematicalLaw ≤
        statDist runtime compiledModel + statDist compiledModel mathematicalLaw :=
      statDist_triangle _ _ _
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          statDist sourceTranscript mathematicalLaw) := by
      exact add_le_add le_rfl (statDist_triangle _ _ _)
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            statDist shaSpecification mathematicalLaw)) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl (statDist_triangle _ _ _))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              statDist shaCollisionIdeal mathematicalLaw))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl (statDist_triangle _ _ _)))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              (statDist shaCollisionIdeal shaPreimageIdeal +
                statDist shaPreimageIdeal mathematicalLaw)))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl
            (add_le_add le_rfl (statDist_triangle _ _ _))))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              (statDist shaCollisionIdeal shaPreimageIdeal +
                (statDist shaPreimageIdeal idealOracle +
                  statDist idealOracle mathematicalLaw))))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl
            (add_le_add le_rfl
              (add_le_add le_rfl (statDist_triangle _ _ _)))))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              (statDist shaCollisionIdeal shaPreimageIdeal +
                (statDist shaPreimageIdeal idealOracle +
                  (statDist idealOracle commitmentModel +
                    statDist commitmentModel mathematicalLaw)))))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl
            (add_le_add le_rfl
              (add_le_add le_rfl
                (add_le_add le_rfl (statDist_triangle _ _ _))))))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              (statDist shaCollisionIdeal shaPreimageIdeal +
                (statDist shaPreimageIdeal idealOracle +
                  (statDist idealOracle commitmentModel +
                    (statDist commitmentModel poseidonSpecification +
                      statDist poseidonSpecification mathematicalLaw))))))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl
            (add_le_add le_rfl
              (add_le_add le_rfl
                (add_le_add le_rfl
                  (add_le_add le_rfl (statDist_triangle _ _ _)))))))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              (statDist shaCollisionIdeal shaPreimageIdeal +
                (statDist shaPreimageIdeal idealOracle +
                  (statDist idealOracle commitmentModel +
                    (statDist commitmentModel poseidonSpecification +
                      (statDist poseidonSpecification poseidonCollisionIdeal +
                        statDist poseidonCollisionIdeal mathematicalLaw)))))))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl
            (add_le_add le_rfl
              (add_le_add le_rfl
                (add_le_add le_rfl
                  (add_le_add le_rfl
                    (add_le_add le_rfl (statDist_triangle _ _ _))))))))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              (statDist shaCollisionIdeal shaPreimageIdeal +
                (statDist shaPreimageIdeal idealOracle +
                  (statDist idealOracle commitmentModel +
                    (statDist commitmentModel poseidonSpecification +
                      (statDist poseidonSpecification poseidonCollisionIdeal +
                        (statDist poseidonCollisionIdeal poseidonPreimageIdeal +
                          statDist poseidonPreimageIdeal mathematicalLaw))))))))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl
            (add_le_add le_rfl
              (add_le_add le_rfl
                (add_le_add le_rfl
                  (add_le_add le_rfl
                    (add_le_add le_rfl
                      (add_le_add le_rfl (statDist_triangle _ _ _)))))))))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              (statDist shaCollisionIdeal shaPreimageIdeal +
                (statDist shaPreimageIdeal idealOracle +
                  (statDist idealOracle commitmentModel +
                    (statDist commitmentModel poseidonSpecification +
                      (statDist poseidonSpecification poseidonCollisionIdeal +
                        (statDist poseidonCollisionIdeal poseidonPreimageIdeal +
                          (statDist poseidonPreimageIdeal entropyIdeal +
                            statDist entropyIdeal mathematicalLaw)))))))))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl
            (add_le_add le_rfl
              (add_le_add le_rfl
                (add_le_add le_rfl
                  (add_le_add le_rfl
                    (add_le_add le_rfl
                      (add_le_add le_rfl
                        (add_le_add le_rfl (statDist_triangle _ _ _))))))))))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              (statDist shaCollisionIdeal shaPreimageIdeal +
                (statDist shaPreimageIdeal idealOracle +
                  (statDist idealOracle commitmentModel +
                    (statDist commitmentModel poseidonSpecification +
                      (statDist poseidonSpecification poseidonCollisionIdeal +
                        (statDist poseidonCollisionIdeal poseidonPreimageIdeal +
                          (statDist poseidonPreimageIdeal entropyIdeal +
                            (statDist entropyIdeal samplerIdeal +
                              statDist samplerIdeal mathematicalLaw))))))))))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl
            (add_le_add le_rfl
              (add_le_add le_rfl
                (add_le_add le_rfl
                  (add_le_add le_rfl
                    (add_le_add le_rfl
                      (add_le_add le_rfl
                        (add_le_add le_rfl
                          (add_le_add le_rfl (statDist_triangle _ _ _)))))))))))
    _ ≤ statDist runtime compiledModel +
        (statDist compiledModel sourceTranscript +
          (statDist sourceTranscript shaSpecification +
            (statDist shaSpecification shaCollisionIdeal +
              (statDist shaCollisionIdeal shaPreimageIdeal +
                (statDist shaPreimageIdeal idealOracle +
                  (statDist idealOracle commitmentModel +
                    (statDist commitmentModel poseidonSpecification +
                      (statDist poseidonSpecification poseidonCollisionIdeal +
                        (statDist poseidonCollisionIdeal poseidonPreimageIdeal +
                          (statDist poseidonPreimageIdeal entropyIdeal +
                            (statDist entropyIdeal samplerIdeal +
                              (statDist samplerIdeal independentSourceIdeal +
                                statDist independentSourceIdeal mathematicalLaw)))))))))))) := by
      exact add_le_add le_rfl
        (add_le_add le_rfl
          (add_le_add le_rfl
            (add_le_add le_rfl
              (add_le_add le_rfl
                (add_le_add le_rfl
                  (add_le_add le_rfl
                    (add_le_add le_rfl
                      (add_le_add le_rfl
                        (add_le_add le_rfl
                          (add_le_add le_rfl
                            (add_le_add le_rfl (statDist_triangle _ _ _))))))))))))
    _ ≤ ε.compiler +
        (ε.rustTranscriptDriver +
          (ε.sha256Implementation +
            (ε.sha256Collision +
              (ε.sha256Preimage +
                (ε.sha256RandomOracle +
                  (ε.commitment +
                    (ε.poseidon2Implementation +
                      (ε.poseidon2Collision +
                        (ε.poseidon2Preimage +
                          (ε.entropyExpander +
                            (ε.rejectionSampler +
                              (ε.sourceIndependence + ε.retrySelection)))))))))))) := by
      exact add_le_add hcompiler
        (add_le_add hrustTranscript
          (add_le_add hshaImplementation
            (add_le_add hshaCollision
              (add_le_add hshaPreimage
                (add_le_add hshaOracle
                  (add_le_add hcommitment
                    (add_le_add hposeidonImplementation
                      (add_le_add hposeidonCollision
                        (add_le_add hposeidonPreimage
                          (add_le_add hentropy
                            (add_le_add hsampler
                              (add_le_add hsource hselection))))))))))))
    _ = ε.total := by
      simp [SideError.total, add_assoc]

/-- If the two mathematical view laws are equal, two deployed views are at
distance at most the sum of the separately audited losses on both sides. -/
theorem deployed_views_close_of_mathematical_hiding
    (left right leftMathematical rightMathematical : PMF View)
    (leftError rightError : SideError)
    (hleft : statDist left leftMathematical ≤ leftError.total)
    (hright : statDist right rightMathematical ≤ rightError.total)
    (hmathematical : leftMathematical = rightMathematical) :
    statDist left right ≤ leftError.total + rightError.total := by
  subst rightMathematical
  exact (statDist_triangle left leftMathematical right).trans
    (add_le_add hleft ((statDist_comm leftMathematical right).trans_le hright))

/-! ## Existing transcript, commitment, and retry results that feed the chain -/

/-- The source-shaped transcript theorem gives exact equality of transcript
output laws as soon as its one remaining universal Rust-driver equality is
proved. -/
theorem transcript_law_matches_source_of_exact_driver
    {RustInput FieldValue PointValue : Type*}
    (inputLaw : PMF RustInput)
    (decodeInput : RustInput → V5TranscriptInputs)
    (decodeDerived : RustInput → V5DerivedValues FieldValue PointValue)
    (rustDriver : RustInput → V5TranscriptDriverResult FieldValue PointValue)
    (hequality : ExactRustV5TranscriptDriverEquality
      decodeInput decodeDerived rustDriver) :
    inputLaw.map rustDriver = inputLaw.map
      (fun input => sourceShapedTranscriptDriver
        (decodeInput input) (decodeDerived input)) := by
  have hdriver : rustDriver = fun input => sourceShapedTranscriptDriver
      (decodeInput input) (decodeDerived input) :=
    funext hequality
  rw [hdriver]

section FixedFunctionCommitment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
variable {V D Tag : Type*}

/-- The existing salted-Merkle theorem instantiates the commitment step for a
fixed hash function.  Its error is one assumed leaf-hiding term per unopened
leaf.  It is not the adaptive oracle-relative commitment theorem still needed
by the deployed Fiat--Shamir compiler. -/
theorem fixed_function_merkle_commitment_step
    {leafH : Tag → V → S → D} {ζ : ℝ≥0∞}
    (hH : SaltHidingHash leafH ζ)
    (t : Tag) (Q : Finset ι) (assignment : ι → V) (placeholder : V) :
    CommitmentHybrid
      (realMT leafH t Q assignment)
      (MTSimulate leafH t Q (fun i _ => assignment i) placeholder)
      (zetaMT (Fintype.card ι) Q.card ζ) :=
  mtSimulate_close hH t Q assignment placeholder

end FixedFunctionCommitment

section ExactComponentCSampler

/-- The ideal iid-u32 proof already follows the source's variable-consumption
shape: each M31 call stops at its first accepted word, aborts after sixteen
rejections, and advances one shared stream through all 4,092 limb calls.  Its
successful law is exactly the earlier block law. -/
theorem ideal_iid_stopping_time_sampler_matches_block_sampler :
    RustIidStreamStoppingTimeMatchesBlockExperiment
      successfulComponentCSequentialCoordinatesLaw :=
  idealIidSequentialStream_matches_preallocatedBlockExperiment

/-- With the explicit M31/CM31/QM31 tower and limb order, the successful
variable-consumption sampler followed by the proved pivot correction is
exactly uniform on the Component-C kernel. -/
theorem exact_qm31_stopping_time_component_c_is_uniform
    (ell : (Fin 1024 → QM31Exact) →ₗ[QM31Exact] QM31Exact)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1) :
    (successfulComponentCStoppingTimeFreeCoordinateLaw
        qm31ExactLimbEquiv).map
      (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv
        ell pivot hpivot) =
      PMF.uniformOfFintype (LinearMap.ker ell) :=
  successfulExactQM31StoppingTimeKernelLaw_eq_uniform ell pivot hpivot

end ExactComponentCSampler

section RetrySelection

variable {Schedule Witness RetryView : Type*}

/-- What the public proof-or-abort boundary retains from the stronger model:
the chosen selector and selected branch view.  Retry count and unselected
schedules are erased.  A production proof must still show that its fixed-time
release controller implements this projection. -/
def releasedSelectionProjection :
    Option (Nat × Fin 3 × Schedule × RetryView) →
      Option (Fin 3 × RetryView)
  | none => none
  | some (_, selected, _, view) => some (selected, view)

/-- The proved cap-17 retry and least-good selection procedure adds no witness
dependence when each released good branch is already witness-independent. -/
theorem retry_selection_preserves_modeled_hiding
    (Good : Schedule → Bool)
    (scheduleLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → Witness → PMF RetryView)
    (left right : Witness)
    (hbranch : ∀ (selected : Fin 3) (schedule : Schedule), Good schedule = true →
      branchView selected schedule left = branchView selected schedule right) :
    AspisV5SelectionHidingAbort.spendComposedLaw Good scheduleLaw branchView left =
      AspisV5SelectionHidingAbort.spendComposedLaw Good scheduleLaw branchView right :=
  AspisV5SelectionHidingAbort.spendComposedLaw_witness_indep
    Good scheduleLaw branchView left right hbranch

/-- The exact public projection also has equal laws.  This closes the purely
functional "what is released" step; it does not claim that the Rust attempt
manager or its entropy source has been identified with `scheduleLaw`. -/
theorem retry_public_release_preserves_modeled_hiding
    (Good : Schedule → Bool)
    (scheduleLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → Witness → PMF RetryView)
    (left right : Witness)
    (hbranch : ∀ (selected : Fin 3) (schedule : Schedule), Good schedule = true →
      branchView selected schedule left = branchView selected schedule right) :
    (AspisV5SelectionHidingAbort.spendComposedLaw
        Good scheduleLaw branchView left).map releasedSelectionProjection =
      (AspisV5SelectionHidingAbort.spendComposedLaw
        Good scheduleLaw branchView right).map releasedSelectionProjection := by
  rw [retry_selection_preserves_modeled_hiding
    Good scheduleLaw branchView left right hbranch]

/-- The one remaining deterministic retry/release seam.  Unlike a test, this
predicate quantifies over every witness and compares the complete production
proof-or-abort law with the cap-17, least-good model after its public
projection. -/
def ExactProductionRetryReleaseCorrespondence
    (productionLaw : Witness → PMF (Option (Fin 3 × RetryView)))
    (Good : Schedule → Bool)
    (scheduleLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → Witness → PMF RetryView) : Prop :=
  ∀ witness, productionLaw witness =
    (AspisV5SelectionHidingAbort.spendComposedLaw
      Good scheduleLaw branchView witness).map releasedSelectionProjection

theorem production_retry_release_hiding_of_exact_correspondence
    (productionLaw : Witness → PMF (Option (Fin 3 × RetryView)))
    (Good : Schedule → Bool)
    (scheduleLaw : PMF (Fin 3 → Schedule))
    (branchView : Fin 3 → Schedule → Witness → PMF RetryView)
    (left right : Witness)
    (hexact : ExactProductionRetryReleaseCorrespondence productionLaw
      Good scheduleLaw branchView)
    (hbranch : ∀ (selected : Fin 3) (schedule : Schedule), Good schedule = true →
      branchView selected schedule left = branchView selected schedule right) :
    productionLaw left = productionLaw right := by
  rw [hexact left, hexact right]
  exact retry_public_release_preserves_modeled_hiding
    Good scheduleLaw branchView left right hbranch

end RetrySelection

/-! ## The strongest existing fixed-schedule mathematical composition -/

section ConcreteFixedScheduleComposition

variable {F K FA MA MH SB PB VA VH VB TB U Encoded : Type*}
variable [Field F] [Field K] [Algebra F K] [Field FA]
variable [AddCommGroup MA] [Module FA MA]
variable [AddCommGroup VA] [Module FA VA]
variable [AddCommGroup MH] [Module K MH]
variable [AddCommGroup SB] [Module K SB]
variable [AddCommGroup PB] [Module K PB]
variable [AddCommGroup VH] [Module K VH]
variable [AddCommGroup VB] [Module K VB]
variable [AddCommGroup U] [Module K U]
variable [Fintype K]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- This is the strongest finite fixed-schedule hiding result currently
available, followed by an arbitrary deterministic encoding.  Its Component-C
coins are the literal successful whole-`u32` experiment and its kernel encoder
is constructed in Lean, so no abstract Component-C sampler or encoder premise
is reintroduced here.  Production entropy, Rust correspondence, commitments,
adaptive transcript compilation, and byte coverage remain outside it. -/
theorem encoded_concrete_fixed_schedule_view_is_witness_independent
    (schedule : CompleteFixedSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (LA : MA →ₗ[FA] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (semantic₁ semantic₂ : MixedOuterSample MA MH SB PB →
      SemanticLane → CWord K)
    (hcopy₁ hcopy₂ componentB₁ componentB₂ :
      MixedOuterSample MA MH SB PB → CWord K)
    (ell : CWord K →ₗ[K] K) (E : CWord K →ₗ[K] U)
    (gamma : K) (hgamma : gamma ≠ 0)
    (publishedInactive : MixedOuterVisible VA VH SB TB VB → K)
    (decodeConditionedRows :
      MixedOuterVisible VA VH SB TB VB → PreCConditionedRows U)
    (hrows₁ : MixedDeployedProjectionCorrespondence
      (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₁ hcopy₁ componentB₁)
    (hrows₂ : MixedDeployedProjectionCorrespondence
      (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      publishedInactive decodeConditionedRows ell E gamma
      semantic₂ hcopy₂ componentB₂)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1)
    (e : QM31Limbs ≃ K)
    (encode : (MixedOuterVisible VA VH SB TB VB × U ×
      (Fin (fRows schedule.fri) → K)) → Encoded) :
    ((PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => successfulSamplerJointKernel ell
          (successfulComponentCFreeCoordinateLaw e)
          (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv
            ell pivot hpivot)
          E (concreteDownstream schedule enc) gamma
          (mixedOuterVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preCWord gamma (semantic₁ sample)
            (hcopy₁ sample) (componentB₁ sample)))).map encode
      = ((PMF.uniformOfFintype (MixedOuterSample MA MH SB PB)).bind
        (fun sample => successfulSamplerJointKernel ell
          (successfulComponentCFreeCoordinateLaw e)
          (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv
            ell pivot hpivot)
          E (concreteDownstream schedule enc) gamma
          (mixedOuterVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preCWord gamma (semantic₂ sample)
            (hcopy₂ sample) (componentB₂ sample)))).map encode := by
  exact congrArg (fun law => law.map encode)
    (concrete_downstream_complete_joint_hiding_conditioned_u32_sampler
      schedule enc LA hLA LH hLH terminalB RB AB hAB
      wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
      semantic₁ semantic₂ hcopy₁ hcopy₂ componentB₁ componentB₂
      ell E gamma hgamma publishedInactive decodeConditionedRows hrows₁ hrows₂
      pivot hpivot e)

end ConcreteFixedScheduleComposition

/-! ## The more general abstract mathematical composition -/

section MathematicalComposition

variable {K MA MH SB PB VA VH VB TB MC U Y Encoded : Type*}
variable [Field K]
variable [AddCommGroup MA] [Module K MA]
variable [AddCommGroup MH] [Module K MH]
variable [AddCommGroup SB] [Module K SB]
variable [AddCommGroup PB] [Module K PB]
variable [AddCommGroup VA] [Module K VA]
variable [AddCommGroup VH] [Module K VH]
variable [AddCommGroup VB] [Module K VB]
variable [AddCommGroup MC] [Module K MC]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup Y] [Module K Y]
variable [DecidableEq K] [Fintype MC]
variable [Fintype MA] [Fintype MH] [Fintype SB] [Fintype PB]

/-- Deterministic encoding cannot undo the exact equality supplied by the
current A/H/B/C mathematical hiding theorem.  `encode` may package every
modeled field, but it is not asserted to be the Rust serializer. -/
theorem encoded_modeled_view_is_witness_independent
    (LA : MA →ₗ[K] VA) (hLA : Function.Surjective LA)
    (LH : MH →ₗ[K] VH) (hLH : Function.Surjective LH)
    (terminalB : SB → TB) (RB : SB →ₗ[K] VB) (AB : PB →ₗ[K] VB)
    (hAB : Function.Surjective AB)
    (wA₁ wA₂ : VA) (wH₁ wH₂ : VH)
    (wBS₁ wBS₂ : SB) (wBV₁ wBV₂ : VB)
    (preC₁ preC₂ : OuterSample MA MH SB PB → MC)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] U) (F : MC →ₗ[K] Y)
    (gamma : K) (hgamma : gamma ≠ 0)
    (publishedInactive : OuterVisible VA VH SB TB VB → K)
    (publishedE : OuterVisible VA VH SB TB VB → U)
    (hprojection₁ : ResidualsAreVisibleProjections
      (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁)
      preC₁ ell E publishedInactive publishedE)
    (hprojection₂ : ResidualsAreVisibleProjections
      (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂)
      preC₂ ell E publishedInactive publishedE)
    (encode : (OuterVisible VA VH SB TB VB × U × Y) → Encoded) :
    ((PMF.uniformOfFintype (OuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (outerVisible LA wA₁ LH wH₁ terminalB RB AB wBS₁ wBV₁ sample)
          (preC₁ sample))).map encode
      = ((PMF.uniformOfFintype (OuterSample MA MH SB PB)).bind
        (fun sample => unconditionedCJointKernel ell E F gamma
          (outerVisible LA wA₂ LH wH₂ terminalB RB AB wBS₂ wBV₂ sample)
          (preC₂ sample))).map encode := by
  exact congrArg (fun law => law.map encode)
    (conditional_complete_joint_hiding_v3
      LA hLA LH hLH terminalB RB AB hAB
      wA₁ wA₂ wH₁ wH₂ wBS₁ wBS₂ wBV₁ wBV₂
      preC₁ preC₂ ell E F gamma hgamma publishedInactive publishedE
      hprojection₁ hprojection₂)

end MathematicalComposition

/-! ## Why the universal production claim still needs bridges -/

/-- Exact equality of ideal mathematical laws does not imply anything about
deployed laws unless the implementation and cryptographic bridges relate the
two experiments.  The countermodel uses equal ideal point masses and unequal
deployed point masses. -/
theorem mathematical_hiding_alone_does_not_imply_deployed_hiding :
    ∃ (idealLeft idealRight deployedLeft deployedRight : PMF Bool),
      idealLeft = idealRight ∧ deployedLeft ≠ deployedRight := by
  refine ⟨PMF.pure false, PMF.pure false, PMF.pure false, PMF.pure true,
    rfl, ?_⟩
  intro heq
  have hvalue := congrArg (fun law : PMF Bool => law false) heq
  simp at hvalue

/-- A compact honest status statement: the current proof body is completely
inventoried, but mathematical hiding alone still cannot establish equality of
two arbitrary deployed distributions.  Applying the conditional hybrid
theorem requires the named code, transcript, commitment, entropy, and runtime
bridges above. -/
theorem repaired_wire_inventory_and_bridge_counterexample :
    Fintype.card (RuntimeBodyByte currentFixtureRuntimeShape) = 75358 ∧
      (∃ (idealLeft idealRight deployedLeft deployedRight : PMF Bool),
        idealLeft = idealRight ∧ deployedLeft ≠ deployedRight) :=
  ⟨current_fixture_runtime_body_has_exactly_75358_classified_bytes,
    mathematical_hiding_alone_does_not_imply_deployed_hiding⟩

/-- Current-release form of the status statement.  All 75,567 bytes are in
the inventory, including the public instruction and sealed account header;
the inventory alone still does not prove that the deployed distribution is
the mathematical one. -/
theorem complete_released_inventory_and_bridge_counterexample :
    Fintype.card ReleasedByteCoordinate = 75567 ∧
      (∃ (idealLeft idealRight deployedLeft deployedRight : PMF Bool),
        idealLeft = idealRight ∧ deployedLeft ≠ deployedRight) :=
  ⟨released_coordinate_count_is_75567,
    mathematical_hiding_alone_does_not_imply_deployed_hiding⟩

#print axioms released_instruction_layout_is_exact
#print axioms released_instruction_field_at_contains
#print axioms every_instruction_offset_has_exactly_one_field
#print axioms sealed_proof_header_layout_is_exact
#print axioms sealed_proof_header_field_at_contains
#print axioms every_sealed_header_offset_has_exactly_one_field
#print axioms releasedByteFin_injective
#print axioms releasedByteFin_surjective
#print axioms every_released_byte_has_exactly_one_class
#print axioms every_released_vector_offset_has_exactly_one_class
#print axioms released_coordinate_count_is_75567
#print axioms released_region_boundaries_are_exact
#print axioms decode_encode_released_byte_parts
#print axioms encode_decode_released_byte_parts
#print axioms fixed_public_data_preserves_proof_body_hiding
#print axioms fixed_public_data_preserves_encoded_hiding
#print axioms released_encoding_law_of_exact_correspondence
#print axioms released_proof_body_byte_count
#print axioms released_instruction_header_and_proof_byte_count
#print axioms every_released_proof_byte_has_exactly_one_class
#print axioms released_selector_position_and_class_are_exact
#print axioms one_side_close_to_mathematical
#print axioms deployed_views_close_of_mathematical_hiding
#print axioms transcript_law_matches_source_of_exact_driver
#print axioms fixed_function_merkle_commitment_step
#print axioms ideal_iid_stopping_time_sampler_matches_block_sampler
#print axioms exact_qm31_stopping_time_component_c_is_uniform
#print axioms retry_selection_preserves_modeled_hiding
#print axioms retry_public_release_preserves_modeled_hiding
#print axioms production_retry_release_hiding_of_exact_correspondence
#print axioms encoded_concrete_fixed_schedule_view_is_witness_independent
#print axioms encoded_modeled_view_is_witness_independent
#print axioms mathematical_hiding_alone_does_not_imply_deployed_hiding
#print axioms repaired_wire_inventory_and_bridge_counterexample
#print axioms complete_released_inventory_and_bridge_counterexample

end AspisV5DeployedZeroKnowledgeBridge
