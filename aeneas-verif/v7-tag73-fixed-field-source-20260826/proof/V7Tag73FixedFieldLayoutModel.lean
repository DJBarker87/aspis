import AspisFormal.K1.V7Tag73DeterministicRefinement
import AspisFormal.K1.V7Tag73FixedFieldMessageBridge

/-!
# Exact packed-field and tape-layout model for production Tag 73

The production proof body carries 641 QM31 values as 2,564 consecutive
31-bit limbs.  This file fixes the bit indices and the canonical mathematical
value exposed by each successful reader call.  It then proves that the exact
16-byte little-endian images written into the Tag-73 tape construct the
existing `FixedFieldDecodeExact` predicate and its `FixedFieldView`.

The later generated-source theorem supplies `TapeCarriesDecodedFixedFields`
from the literal translated verifier execution; it is not an acceptance or
parser-correctness assumption.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace AspisV7Tag73FixedFieldLayoutModel

open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact
open AspisV6TranscriptRelationGrammar
open AspisV6AcceptedPathObligations

abbrev FixedFieldCount : Nat := 641
abbrev LimbsPerQM31 : Nat := 4
abbrev PackedLimbBits : Nat := 31
abbrev FixedLimbCount : Nat := FixedFieldCount * LimbsPerQM31
abbrev FixedMeaningfulBits : Nat := FixedLimbCount * PackedLimbBits
abbrev FixedPackedBytes : Nat := (FixedMeaningfulBits + 7) / 8

abbrev InitialFieldCount : Nat := 1
abbrev SemanticFieldCount : Nat := 10 * 27
abbrev PointClaimFieldCount : Nat := 3 * 29
abbrev InactiveFieldCount : Nat := 1
abbrev OodFieldCount : Nat := 2
abbrev RelationFieldCount : Nat := 4 * 6
abbrev FinalFieldCount : Nat := 256

abbrev V7DigestBytes : Nat := 26
abbrev V7WorkNonceBytes : Nat := 24
abbrev V7QueryCount : Nat := 16
abbrev V7C1BytesPerQuery : Nat := 403
abbrev V7C2BytesPerQuery : Nat := 186
abbrev V7SaltBytesPerQuery : Nat := 32
abbrev V7QueryBytes : Nat :=
  V7C1BytesPerQuery + V7C2BytesPerQuery + V7SaltBytesPerQuery
abbrev V7QuerySectionBytes : Nat := V7QueryCount * V7QueryBytes
abbrev V7FixedSectionOffset : Nat := 0
abbrev V7C1RootOffset : Nat := FixedPackedBytes
abbrev V7C2RootOffset : Nat := V7C1RootOffset + V7DigestBytes
abbrev V7WorkNoncesOffset : Nat := V7C2RootOffset + V7DigestBytes
abbrev V7QuerySectionOffset : Nat := V7WorkNoncesOffset + V7WorkNonceBytes
abbrev V7BodyWithoutFrontiers : Nat :=
  V7QuerySectionOffset + V7QuerySectionBytes

theorem fixed_field_partition_exact :
    InitialFieldCount + SemanticFieldCount + PointClaimFieldCount +
      InactiveFieldCount + OodFieldCount + RelationFieldCount +
      FinalFieldCount = FixedFieldCount := by
  norm_num [InitialFieldCount, SemanticFieldCount, PointClaimFieldCount,
    InactiveFieldCount, OodFieldCount, RelationFieldCount, FinalFieldCount,
    FixedFieldCount]

theorem fixed_limb_count_exact : FixedLimbCount = 2564 := by
  norm_num [FixedLimbCount, FixedFieldCount, LimbsPerQM31]

theorem fixed_meaningful_bits_exact : FixedMeaningfulBits = 79484 := by
  norm_num [FixedMeaningfulBits, FixedLimbCount, FixedFieldCount,
    LimbsPerQM31, PackedLimbBits]

theorem fixed_packed_bytes_exact : FixedPackedBytes = 9936 := by
  norm_num [FixedPackedBytes, FixedMeaningfulBits, FixedLimbCount,
    FixedFieldCount, LimbsPerQM31, PackedLimbBits]

theorem fixed_padding_bits_exact :
    FixedPackedBytes * 8 - FixedMeaningfulBits = 4 := by
  norm_num [FixedPackedBytes, FixedMeaningfulBits, FixedLimbCount,
    FixedFieldCount, LimbsPerQM31, PackedLimbBits]

theorem v7_query_bytes_exact : V7QueryBytes = 621 := by
  norm_num [V7QueryBytes, V7C1BytesPerQuery, V7C2BytesPerQuery,
    V7SaltBytesPerQuery]

theorem v7_query_section_bytes_exact : V7QuerySectionBytes = 9936 := by
  norm_num [V7QuerySectionBytes, V7QueryCount, V7QueryBytes,
    V7C1BytesPerQuery, V7C2BytesPerQuery, V7SaltBytesPerQuery]

theorem v7_fixed_and_following_offsets_exact :
    V7FixedSectionOffset = 0 ∧
    V7C1RootOffset = 9936 ∧
    V7C2RootOffset = 9962 ∧
    V7WorkNoncesOffset = 9988 ∧
    V7QuerySectionOffset = 10012 ∧
    V7BodyWithoutFrontiers = 19948 := by
  norm_num [V7FixedSectionOffset, V7C1RootOffset, V7C2RootOffset,
    V7WorkNoncesOffset, V7QuerySectionOffset, V7BodyWithoutFrontiers,
    V7DigestBytes, V7WorkNonceBytes, V7QuerySectionBytes, V7QueryCount,
    V7QueryBytes, V7C1BytesPerQuery, V7C2BytesPerQuery,
    V7SaltBytesPerQuery, FixedPackedBytes, FixedMeaningfulBits,
    FixedLimbCount, FixedFieldCount, LimbsPerQM31, PackedLimbBits]

theorem v7_exact_body_length_with_frontiers (frontierNodes : Nat) :
    V7BodyWithoutFrontiers + 2 * (frontierNodes * V7DigestBytes) =
      19948 + 52 * frontierNodes := by
  norm_num [V7BodyWithoutFrontiers, V7QuerySectionOffset,
    V7WorkNoncesOffset, V7C2RootOffset, V7C1RootOffset, V7DigestBytes,
    V7WorkNonceBytes, V7QuerySectionBytes, V7QueryCount, V7QueryBytes,
    V7C1BytesPerQuery, V7C2BytesPerQuery, V7SaltBytesPerQuery,
    FixedPackedBytes, FixedMeaningfulBits, FixedLimbCount, FixedFieldCount,
    LimbsPerQM31, PackedLimbBits]
  omega

theorem v7_maximum_body_length_exact :
    V7BodyWithoutFrontiers + 2 * (203 * V7DigestBytes) = 30504 := by
  norm_num [V7BodyWithoutFrontiers, V7QuerySectionOffset,
    V7WorkNoncesOffset, V7C2RootOffset, V7C1RootOffset, V7DigestBytes,
    V7WorkNonceBytes, V7QuerySectionBytes, V7QueryCount, V7QueryBytes,
    V7C1BytesPerQuery, V7C2BytesPerQuery, V7SaltBytesPerQuery,
    FixedPackedBytes, FixedMeaningfulBits, FixedLimbCount, FixedFieldCount,
    LimbsPerQM31, PackedLimbBits]

/-- Global packed-limb index for one fixed field in production tower order
`(c0.a,c0.b,c1.a,c1.b)`. -/
def fixedLimbIndex (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    Fin FixedLimbCount :=
  ⟨field.val * LimbsPerQM31 + limb.val, by
    simp only [FixedLimbCount]
    nlinarith [field.isLt, limb.isLt]⟩

@[simp] theorem fixedLimbIndex_val
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    (fixedLimbIndex field limb : Nat) = field.val * 4 + limb.val := by
  rfl

/-- First global bit of a packed limb.  Production's streaming reader takes
the next 31 low-to-high bits beginning at this offset. -/
def fixedLimbBitStart (field : Fin FixedFieldCount)
    (limb : Fin LimbsPerQM31) : Nat :=
  (fixedLimbIndex field limb).val * PackedLimbBits

@[simp] theorem fixedLimbBitStart_val
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    fixedLimbBitStart field limb = (field.val * 4 + limb.val) * 31 := by
  rfl

theorem fixed_last_limb_exact_range :
    fixedLimbBitStart ⟨640, by norm_num [FixedFieldCount]⟩
        ⟨3, by norm_num [LimbsPerQM31]⟩ = 79453 ∧
      fixedLimbBitStart ⟨640, by norm_num [FixedFieldCount]⟩
        ⟨3, by norm_num [LimbsPerQM31]⟩ + 31 = 79484 := by
  norm_num [fixedLimbBitStart, fixedLimbIndex, PackedLimbBits,
    LimbsPerQM31]

theorem fixedLimbBitStart_within_meaningful
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    fixedLimbBitStart field limb + 31 ≤ FixedMeaningfulBits := by
  simp only [fixedLimbBitStart, FixedMeaningfulBits, PackedLimbBits]
  have h := (fixedLimbIndex field limb).isLt
  omega

/-- Byte containing the first bit and the intra-byte shift used by
`packed_m31_at` and by the streaming reader's equivalent bit buffer. -/
def fixedLimbByteStart (field : Fin FixedFieldCount)
    (limb : Fin LimbsPerQM31) : Nat :=
  fixedLimbBitStart field limb / 8

def fixedLimbByteShift (field : Fin FixedFieldCount)
    (limb : Fin LimbsPerQM31) : Nat :=
  fixedLimbBitStart field limb % 8

theorem fixedLimbByteShift_lt_eight
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    fixedLimbByteShift field limb < 8 := by
  exact Nat.mod_lt _ (by norm_num)

theorem fixedLimbFiveByteWindow_within_packed
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    fixedLimbByteStart field limb + 4 < FixedPackedBytes := by
  have hIndex := (fixedLimbIndex field limb).isLt
  simp only [fixedLimbByteStart, fixedLimbBitStart, FixedPackedBytes,
    FixedMeaningfulBits, FixedLimbCount, FixedFieldCount, LimbsPerQM31,
    PackedLimbBits] at *
  omega

theorem fixedLimbBitStart_byte_decomposition
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    fixedLimbBitStart field limb =
      8 * fixedLimbByteStart field limb + fixedLimbByteShift field limb := by
  calc
    fixedLimbBitStart field limb =
        fixedLimbBitStart field limb % 8 +
          8 * (fixedLimbBitStart field limb / 8) :=
      (Nat.mod_add_div (fixedLimbBitStart field limb) 8).symm
    _ = 8 * fixedLimbByteStart field limb +
        fixedLimbByteShift field limb := by
      simp only [fixedLimbByteStart, fixedLimbByteShift, Nat.add_comm]

/-- Inverse field projection for a global packed-limb ordinal. -/
def fieldAtLimbOrdinal (ordinal : Fin FixedLimbCount) :
    Fin FixedFieldCount :=
  ⟨ordinal.val / LimbsPerQM31, by
    have ordinalLt := ordinal.isLt
    simp only [FixedLimbCount, FixedFieldCount, LimbsPerQM31] at ordinalLt ⊢
    omega⟩

/-- Inverse within-QM31 limb projection for a global packed-limb ordinal. -/
def limbAtLimbOrdinal (ordinal : Fin FixedLimbCount) :
    Fin LimbsPerQM31 :=
  ⟨ordinal.val % LimbsPerQM31, Nat.mod_lt _ (by
    norm_num [LimbsPerQM31])⟩

theorem fixedLimbIndex_inverse
    (ordinal : Fin FixedLimbCount) :
    fixedLimbIndex (fieldAtLimbOrdinal ordinal)
      (limbAtLimbOrdinal ordinal) = ordinal := by
  apply Fin.ext
  simp only [fixedLimbIndex_val, fieldAtLimbOrdinal, limbAtLimbOrdinal,
    LimbsPerQM31]
  omega

theorem fieldAtLimbOrdinal_fixedLimbIndex
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    fieldAtLimbOrdinal (fixedLimbIndex field limb) = field := by
  apply Fin.ext
  simp only [fieldAtLimbOrdinal, fixedLimbIndex_val, LimbsPerQM31]
  have limbLt := limb.isLt
  norm_num [LimbsPerQM31] at limbLt
  omega

theorem limbAtLimbOrdinal_fixedLimbIndex
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    limbAtLimbOrdinal (fixedLimbIndex field limb) = limb := by
  apply Fin.ext
  simp only [limbAtLimbOrdinal, fixedLimbIndex_val, LimbsPerQM31]
  have limbLt := limb.isLt
  norm_num [LimbsPerQM31] at limbLt
  omega

theorem fixedLimbBitStart_at_ordinal
    (ordinal : Fin FixedLimbCount) :
    fixedLimbBitStart (fieldAtLimbOrdinal ordinal)
        (limbAtLimbOrdinal ordinal) = ordinal.val * 31 := by
  unfold fixedLimbBitStart
  rw [fixedLimbIndex_inverse]

/-! ## Exact streaming-reader geometry

The Aeneas proof uses these closed arithmetic facts to relate the state
threaded by `PackedM31Reader::next` to the global limb ordinal.  They are
stated independently of the generated namespace so the source-facing file
only has to prove the byte/buffer contents, not repeat the 2,564-index
arithmetic. -/

/-- Byte index already loaded by the streaming reader immediately before
global packed-limb ordinal `ordinal`.  This is the ceiling of the consumed
bit count divided by eight. -/
def readerByteIndexAtLimb (ordinal : Nat) : Nat :=
  (ordinal * PackedLimbBits + 7) / 8

/-- Number of still-unconsumed bits in the source reader's `u64` buffer
immediately before global packed-limb ordinal `ordinal`. -/
def readerBufferedBitsAtLimb (ordinal : Nat) : Nat :=
  readerByteIndexAtLimb ordinal * 8 - ordinal * PackedLimbBits

theorem reader_state_eight_limb_cycle
    (block slot : Nat) (slotLt : slot < 8) :
    readerByteIndexAtLimb (8 * block + slot) =
        31 * block + (31 * slot + 7) / 8 ∧
      readerBufferedBitsAtLimb (8 * block + slot) = slot := by
  constructor <;>
    simp only [readerByteIndexAtLimb, readerBufferedBitsAtLimb,
    PackedLimbBits] <;>
    omega

/-- Seven calls in each eight-limb cycle load four new bytes; the eighth
loads three and returns the reader to a byte boundary. -/
theorem reader_next_byte_count_eight_limb_cycle
    (block slot : Nat) (slotLt : slot < 8) :
    readerByteIndexAtLimb (8 * block + slot + 1) -
        readerByteIndexAtLimb (8 * block + slot) =
      if slot = 7 then 3 else 4 := by
  simp only [readerByteIndexAtLimb, PackedLimbBits]
  split <;> omega

theorem reader_state_full_cycle_advance (block : Nat) :
    readerByteIndexAtLimb (8 * (block + 1)) =
        readerByteIndexAtLimb (8 * block) + 31 ∧
      readerBufferedBitsAtLimb (8 * block) = 0 ∧
      readerBufferedBitsAtLimb (8 * (block + 1)) = 0 := by
  have current := reader_state_eight_limb_cycle block 0 (by omega)
  have next := reader_state_eight_limb_cycle (block + 1) 0 (by omega)
  simp only [Nat.add_zero] at current next
  omega

theorem reader_state_after_320_full_cycles :
    readerByteIndexAtLimb 2560 = 9920 ∧
      readerBufferedBitsAtLimb 2560 = 0 := by
  norm_num [readerByteIndexAtLimb, readerBufferedBitsAtLimb,
    PackedLimbBits]

theorem reader_state_after_all_fixed_limbs :
    readerByteIndexAtLimb 2564 = 9936 ∧
      readerBufferedBitsAtLimb 2564 = 4 := by
  norm_num [readerByteIndexAtLimb, readerBufferedBitsAtLimb,
    PackedLimbBits]

theorem reader_final_four_limb_byte_span :
    readerByteIndexAtLimb 2560 = 9920 ∧
      readerByteIndexAtLimb 2564 = 9936 ∧
      readerByteIndexAtLimb 2564 - readerByteIndexAtLimb 2560 = 16 := by
  norm_num [readerByteIndexAtLimb, PackedLimbBits]

/-! ## Exact packed-section to transcript-message map -/

/-- The parser's exact first 9,936 bytes, represented independently of the
Aeneas slice type. -/
abbrev PackedFixedSection := Fin 9936 → Fin 256

/-- Total byte lookup used by the five-byte low-31 window.  The zero branch is
unreachable for all 2,564 frozen limb starts; keeping it total makes the model
independent of proof-irrelevant index witnesses. -/
def packedSectionByte (packed : PackedFixedSection) (index : Nat) : Fin 256 :=
  if h : index < 9936 then packed ⟨index, h⟩ else 0

theorem packedSectionByte_eq (packed : PackedFixedSection) (index : Nat)
    (within : index < 9936) :
    packedSectionByte packed index = packed ⟨index, within⟩ := by
  simp [packedSectionByte, within]

/-- Literal little-endian five-byte window beginning at the byte containing
the limb's first bit. -/
def packedLimbWindow (packed : PackedFixedSection)
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) : Nat :=
  ∑ offset : Fin 5,
    (packedSectionByte packed (fixedLimbByteStart field limb + offset.val) : Nat) *
      256 ^ offset.val

/-- The production limb value: shift away the intra-byte prefix and retain
exactly the next 31 low bits. -/
def packedLimbNat (packed : PackedFixedSection)
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) : Nat :=
  (packedLimbWindow packed field limb / 2 ^ fixedLimbByteShift field limb) %
    2 ^ 31

theorem packedLimbNat_lt_two_pow_31 (packed : PackedFixedSection)
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) :
    packedLimbNat packed field limb < 2 ^ 31 := by
  exact Nat.mod_lt _ (by norm_num)

/-- The same accepted 31-bit word viewed as the source codec's `u32`. -/
def packedLimbRawWord (packed : PackedFixedSection)
    (field : Fin FixedFieldCount) (limb : Fin LimbsPerQM31) : RawWord :=
  ⟨packedLimbNat packed field limb, by
    have h := packedLimbNat_lt_two_pow_31 packed field limb
    norm_num [rawWordCount] at h ⊢
    omega⟩

/-- Canonicality is not built into the byte layout.  It is the exact strict
comparison established by each successful production `next_qm31` call. -/
def PackedFixedSectionCanonical (packed : PackedFixedSection) : Prop :=
  ∀ field limb, packedLimbNat packed field limb < m31Modulus

theorem packedFixedSectionCanonical_of_every_ordinal
    (packed : PackedFixedSection)
    (everyOrdinal : ∀ ordinal : Fin FixedLimbCount,
      packedLimbNat packed (fieldAtLimbOrdinal ordinal)
          (limbAtLimbOrdinal ordinal) < m31Modulus) :
    PackedFixedSectionCanonical packed := by
  intro field limb
  simpa [fieldAtLimbOrdinal_fixedLimbIndex,
    limbAtLimbOrdinal_fixedLimbIndex] using
    everyOrdinal (fixedLimbIndex field limb)

/-- Exact parser-side uniqueness condition for the otherwise-unused high
nibble of byte 9,935. -/
def PackedFixedPaddingZero (packed : PackedFixedSection) : Prop :=
  (packed ⟨9935, by norm_num⟩ : Nat) < 16

/-- Complete source-independent well-formedness of the fixed packed section.
The section length is already fixed by `PackedFixedSection`; the two fields
are exactly the parser's unused-high-nibble check and the 2,564 strict M31
comparisons supplied by successful fixed-reader calls. -/
structure ExactCanonicalPackedFixedSection
    (packed : PackedFixedSection) : Prop where
  paddingZero : PackedFixedPaddingZero packed
  canonical : PackedFixedSectionCanonical packed

/-- The bundle's byte-level padding predicate is definitionally the frozen
grammar's canonical fixed-padding predicate on byte 9,935. -/
theorem packedFixedPaddingZero_iff_canonicalFixedPadding
    (packed : PackedFixedSection) :
    PackedFixedPaddingZero packed ↔
      CanonicalFixedPadding (packed ⟨9935, by norm_num⟩) := by
  rfl

/-- Four source-order little-endian words for one packed field, without
assuming canonicality. -/
def packedFieldMessageBytes (packed : PackedFixedSection)
    (field : Fin FixedFieldCount) : Qm31Bytes :=
  fun offset =>
    let position := finProdFinEquiv.symm offset
    tagByteEquivExactByte.symm
      (encodeWordLE (packedLimbRawWord packed field position.1) position.2)

/-- Primitive input correspondence: the fixed transcript tape records the
four little-endian words extracted from the parser's first 9,936 bytes.  This
relation says nothing about canonicality or decoder success. -/
def PackedFixedMessagesMatch (tape : DeployedFixedTape)
    (packed : PackedFixedSection) : Prop :=
  ∀ field,
    rawFixedFieldBytes (rawOfMessages tape.messages) field =
      packedFieldMessageBytes packed field

/-- Replace only the 641 prover-controlled fixed-field messages by the exact
little-endian images extracted from a production packed section.  Every
non-fixed prover message and every verifier-derived value is preserved. -/
def rawWithPackedFixedFields (raw : RawTag73ProverMessages)
    (packed : PackedFixedSection) : RawTag73ProverMessages :=
  { raw with
    initialClaim := packedFieldMessageBytes packed ⟨0, by norm_num⟩
    semanticSent := fun round sent =>
      packedFieldMessageBytes packed (semanticFieldIndex round sent)
    pointClaims := fun row column =>
      packedFieldMessageBytes packed (pointClaimFieldIndex row column)
    inactiveClaim := packedFieldMessageBytes packed ⟨358, by norm_num⟩
    oodValue := fun sample =>
      packedFieldMessageBytes packed (oodFieldIndex sample)
    relationSent := fun round sent =>
      packedFieldMessageBytes packed (relationFieldIndex round sent)
    finalValues := fun coefficient =>
      packedFieldMessageBytes packed (finalFieldIndex coefficient) }

/-- The piecewise frozen layout is an exact inverse of the seven production
storage sections. -/
theorem rawFixedFieldBytes_rawWithPackedFixedFields
    (raw : RawTag73ProverMessages) (packed : PackedFixedSection)
    (field : Fin FixedFieldCount) :
    rawFixedFieldBytes (rawWithPackedFixedFields raw packed) field =
      packedFieldMessageBytes packed field := by
  unfold rawFixedFieldBytes
  simp only [rawWithPackedFixedFields]
  split_ifs with initial semantic point inactive ood relation
  · congr 1
    apply Fin.ext
    simpa using initial.symm
  · congr 1
    apply Fin.ext
    simp only [semanticFieldIndex, Fin.val_mk]
    omega
  · congr 1
    apply Fin.ext
    simp only [pointClaimFieldIndex, Fin.val_mk]
    omega
  · congr 1
    apply Fin.ext
    simpa using inactive.symm
  · congr 1
    apply Fin.ext
    simp only [oodFieldIndex, Fin.val_mk]
    omega
  · congr 1
    apply Fin.ext
    simp only [relationFieldIndex, Fin.val_mk]
    omega
  · congr 1
    apply Fin.ext
    simp only [finalFieldIndex, Fin.val_mk]
    omega

/-- Rebuild the convenient transcript-message record with the exact source
fixed fields while retaining its challenge values, sampler uses, grinding
histories, roots, nonces, and query-batch claim. -/
def messagesWithPackedFixedFields (messages : Messages)
    (packed : PackedFixedSection) : Messages :=
  (rawWithPackedFixedFields (rawOfMessages messages) packed).withDerived
    messages.challengeValue messages.challengeUse
    messages.batchGrinding.probesBeforeSelected
    messages.foldGrinding.probesBeforeSelected
    messages.finalGrinding.probesBeforeSelected

theorem rawOfMessages_messagesWithPackedFixedFields
    (messages : Messages) (packed : PackedFixedSection) :
    rawOfMessages (messagesWithPackedFixedFields messages packed) =
      rawWithPackedFixedFields (rawOfMessages messages) packed := by
  exact rawOfMessages_withDerived _ _ _ _ _ _

/-- Canonical source projection on a complete fixed tape.  The search witness,
frontier counts, and secure-circle returns do not depend on the fixed-field
message representation and are preserved definitionally. -/
def tapeWithPackedFixedFields (tape : DeployedFixedTape)
    (packed : PackedFixedSection) : DeployedFixedTape :=
  { tape with messages := messagesWithPackedFixedFields tape.messages packed }

theorem tapeWithPackedFixedFields_messages_match
    (tape : DeployedFixedTape) (packed : PackedFixedSection) :
    PackedFixedMessagesMatch (tapeWithPackedFixedFields tape packed) packed := by
  intro field
  change rawFixedFieldBytes
      (rawOfMessages (messagesWithPackedFixedFields tape.messages packed)) field =
    packedFieldMessageBytes packed field
  rw [rawOfMessages_messagesWithPackedFixedFields]
  exact rawFixedFieldBytes_rawWithPackedFixedFields _ _ _

/-- The unique exact-tower family obtained after the source has established
all four strict M31 comparisons for every field. -/
def decodedPackedFields (packed : PackedFixedSection)
    (canonical : PackedFixedSectionCanonical packed) :
    Fin FixedFieldCount → QM31Exact :=
  fun field => limbsToQM31Exact (fun limb =>
    ⟨packedLimbNat packed field limb, canonical field limb⟩)

/-- The frozen typed view determined by one canonical packed section.  Unlike
an arbitrary `stored` view, this object contains no equality premise: it is
constructed directly from the 641 source-order decoded values. -/
def packedFixedFieldView (packed : PackedFixedSection)
    (canonical : PackedFixedSectionCanonical packed) :
    FixedFieldView QM31Exact :=
  decodedFixedFieldView (decodedPackedFields packed canonical)

theorem packedFieldMessageBytes_eq_encodeTagQM31ExactLE
    (packed : PackedFixedSection)
    (canonical : PackedFixedSectionCanonical packed)
    (field : Fin FixedFieldCount) :
    packedFieldMessageBytes packed field =
      encodeTagQM31ExactLE (decodedPackedFields packed canonical field) := by
  funext offset
  apply tagByteEquivExactByte.injective
  simp [packedFieldMessageBytes, encodeTagQM31ExactLE,
    exactQm31BytesToTag, encodeQM31ExactLE, encodeQM31LE,
    decodedPackedFields, packedLimbRawWord, encodeM31LE, m31AsRawWord]
  simp [finProdFinEquiv]

/-- Replacing the seven raw fixed-field sections by the bytes extracted from
one canonical packed section directly establishes the frozen decoder
predicate.  No independently supplied tape/input relation is required. -/
theorem rawWithPackedFixedFields_fixedFieldDecodeExact
    (raw : RawTag73ProverMessages) (packed : PackedFixedSection)
    (canonical : PackedFixedSectionCanonical packed) :
    FixedFieldDecodeExact (rawWithPackedFixedFields raw packed)
      (decodedPackedFields packed canonical) := by
  intro field
  rw [rawFixedFieldBytes_rawWithPackedFixedFields]
  rw [packedFieldMessageBytes_eq_encodeTagQM31ExactLE packed canonical field]
  exact decodeTagQM31ExactLE_encodeTagQM31ExactLE
    (decodedPackedFields packed canonical field)

/-- Strong source-independent raw-message capstone.  Exact packed-section
well-formedness constructs both the existing decoder witness and its frozen
typed view, while retaining the parser's canonical-padding fact explicitly. -/
theorem exactCanonicalPackedSection_constructs_raw_decode_and_view
    (raw : RawTag73ProverMessages) (packed : PackedFixedSection)
    (exact : ExactCanonicalPackedFixedSection packed) :
    ∃ decoded : Fin 641 → QM31Exact,
      FixedFieldDecodeExact (rawWithPackedFixedFields raw packed) decoded ∧
      packedFixedFieldView packed exact.canonical =
        decodedFixedFieldView decoded ∧
      CanonicalFixedPadding (packed ⟨9935, by norm_num⟩) := by
  refine ⟨decodedPackedFields packed exact.canonical, ?_, rfl, ?_⟩
  · exact rawWithPackedFixedFields_fixedFieldDecodeExact
      raw packed exact.canonical
  · exact
      (packedFixedPaddingZero_iff_canonicalFixedPadding packed).mp
        exact.paddingZero

/-- The exact family of canonical values returned by 641 successful source
reader calls. -/
abbrev DecodedFixedFields := Fin FixedFieldCount → QM31Exact

/-- Representation relation between the production values and the existing
fixed-tape model.  This says only that the tape contains the literal
`QM31::write_le_bytes` image of each value at the frozen layout index. -/
def TapeCarriesDecodedFixedFields
    (tape : DeployedFixedTape) (decoded : DecodedFixedFields) : Prop :=
  ∀ index,
    rawFixedFieldBytes (rawOfMessages tape.messages) index =
      encodeTagQM31ExactLE (decoded index)

theorem packedFixedMessagesMatch_tapeCarriesDecodedFixedFields
    {tape : DeployedFixedTape} {packed : PackedFixedSection}
    (messages : PackedFixedMessagesMatch tape packed)
    (canonical : PackedFixedSectionCanonical packed) :
    TapeCarriesDecodedFixedFields tape
      (decodedPackedFields packed canonical) := by
  intro field
  rw [messages field]
  exact packedFieldMessageBytes_eq_encodeTagQM31ExactLE packed canonical field

/-- Exact production/tape bytes construct the decoder predicate required by
the existing semantic and relation bridge. -/
theorem tapeCarriesDecodedFixedFields_fixedFieldDecodeExact
    {tape : DeployedFixedTape} {decoded : DecodedFixedFields}
    (binding : TapeCarriesDecodedFixedFields tape decoded) :
    FixedFieldDecodeExact (rawOfMessages tape.messages) decoded := by
  intro index
  rw [binding index]
  exact decodeTagQM31ExactLE_encodeTagQM31ExactLE (decoded index)

/-- Requested existential form, choice-free because the decoded family is
the exact family returned by the source reader trace. -/
theorem tapeCarriesDecodedFixedFields_constructs_exact_decode
    {tape : DeployedFixedTape} {decoded : DecodedFixedFields}
    (binding : TapeCarriesDecodedFixedFields tape decoded) :
    ∃ decoded : Fin 641 → QM31Exact,
      FixedFieldDecodeExact (rawOfMessages tape.messages) decoded := by
  exact ⟨decoded,
    tapeCarriesDecodedFixedFields_fixedFieldDecodeExact binding⟩

/-- Parser-section/tape byte identity plus the strict comparisons supplied by
literal successful reader calls produce the requested exact decoder witness. -/
theorem packedFixedMessagesMatch_constructs_exact_decode
    {tape : DeployedFixedTape} {packed : PackedFixedSection}
    (messages : PackedFixedMessagesMatch tape packed)
    (canonical : PackedFixedSectionCanonical packed) :
    ∃ decoded : Fin 641 → QM31Exact,
      FixedFieldDecodeExact (rawOfMessages tape.messages) decoded := by
  exact tapeCarriesDecodedFixedFields_constructs_exact_decode
    (packedFixedMessagesMatch_tapeCarriesDecodedFixedFields messages canonical)

/-- Once translated production success supplies the strict limb comparisons,
the canonical tape projection needs no separately assumed tape/input binding:
its fixed messages are constructed from the parser slice itself. -/
theorem tapeWithPackedFixedFields_constructs_exact_decode
    (tape : DeployedFixedTape) (packed : PackedFixedSection)
    (canonical : PackedFixedSectionCanonical packed) :
    ∃ decoded : Fin 641 → QM31Exact,
      FixedFieldDecodeExact
        (rawOfMessages (tapeWithPackedFixedFields tape packed).messages)
        decoded := by
  exact packedFixedMessagesMatch_constructs_exact_decode
    (tapeWithPackedFixedFields_messages_match tape packed) canonical

/-- Strong projected-tape capstone.  The projection preserves every
non-fixed prover message and every verifier-derived field, and its fixed
messages obtain both the exact frozen decode and the canonical typed view
without a tape/input or stored-view premise. -/
theorem exactCanonicalPackedSection_constructs_projected_decode_and_view
    (tape : DeployedFixedTape) (packed : PackedFixedSection)
    (exact : ExactCanonicalPackedFixedSection packed) :
    ∃ decoded : Fin 641 → QM31Exact,
      FixedFieldDecodeExact
          (rawOfMessages (tapeWithPackedFixedFields tape packed).messages)
          decoded ∧
      packedFixedFieldView packed exact.canonical =
        decodedFixedFieldView decoded ∧
      CanonicalFixedPadding (packed ⟨9935, by norm_num⟩) := by
  refine ⟨decodedPackedFields packed exact.canonical, ?_, rfl, ?_⟩
  · exact tapeCarriesDecodedFixedFields_fixedFieldDecodeExact
      (packedFixedMessagesMatch_tapeCarriesDecodedFixedFields
        (tapeWithPackedFixedFields_messages_match tape packed)
        exact.canonical)
  · exact
      (packedFixedPaddingZero_iff_canonicalFixedPadding packed).mp
        exact.paddingZero

/-- Companion for an independently supplied tape.  Its sole representation
premise is primitive byte identity; canonicality, decoder success, the view,
and canonical padding are all produced by the theorem. -/
theorem packedFixedMessagesMatch_constructs_exact_decode_and_canonical_view
    {tape : DeployedFixedTape} {packed : PackedFixedSection}
    (messages : PackedFixedMessagesMatch tape packed)
    (exact : ExactCanonicalPackedFixedSection packed) :
    ∃ decoded : Fin 641 → QM31Exact,
      FixedFieldDecodeExact (rawOfMessages tape.messages) decoded ∧
      packedFixedFieldView packed exact.canonical =
        decodedFixedFieldView decoded ∧
      CanonicalFixedPadding (packed ⟨9935, by norm_num⟩) := by
  refine ⟨decodedPackedFields packed exact.canonical, ?_, rfl, ?_⟩
  · exact tapeCarriesDecodedFixedFields_fixedFieldDecodeExact
      (packedFixedMessagesMatch_tapeCarriesDecodedFixedFields
        messages exact.canonical)
  · exact
      (packedFixedPaddingZero_iff_canonicalFixedPadding packed).mp
        exact.paddingZero

/-- Projection-by-projection form of the typed fixed-field view equality.
This compatibility relation is useful only after generated source equations
have established every field.  It must not be assumed by the source capstone:
for an arbitrary `stored` value its fields already contain the desired
extensional view equality. -/
structure StoredFixedFieldViewExact
    (stored : FixedFieldView QM31Exact) (decoded : DecodedFixedFields) : Prop where
  initialClaim : stored.initialClaim = decoded ⟨0, by norm_num [FixedFieldCount]⟩
  semanticSent : ∀ round sent,
    stored.semanticSent round sent = decoded (semanticFieldIndex round sent)
  pointClaim : ∀ row column,
    stored.pointClaim row column = decoded (pointClaimFieldIndex row column)
  inactiveClaim : stored.inactiveClaim =
    decoded ⟨358, by norm_num [FixedFieldCount]⟩
  oodValue : ∀ sample,
    stored.oodValue sample = decoded (oodFieldIndex sample)
  relationSent : ∀ round sent,
    stored.relationSent round sent = decoded (relationFieldIndex round sent)
  finalCoefficient : ∀ coefficient,
    stored.finalCoefficient coefficient = decoded (finalFieldIndex coefficient)

theorem storedFixedFieldViewExact_eq_decodedFixedFieldView
    {stored : FixedFieldView QM31Exact} {decoded : DecodedFixedFields}
    (viewExact : StoredFixedFieldViewExact stored decoded) :
    stored = decodedFixedFieldView decoded := by
  cases stored with
  | mk initial semantic point inactive ood relation final =>
      simp only [decodedFixedFieldView]
      congr
      · exact viewExact.initialClaim
      · funext round sent
        exact viewExact.semanticSent round sent
      · funext row column
        exact viewExact.pointClaim row column
      · exact viewExact.inactiveClaim
      · funext sample
        exact viewExact.oodValue sample
      · funext round sent
        exact viewExact.relationSent round sent
      · funext coefficient
        exact viewExact.finalCoefficient coefficient

/-- The view constructed from the packed section satisfies the compatibility
relation internally, with no stored-view hypothesis. -/
theorem packedFixedFieldView_storedFixedFieldViewExact
    (packed : PackedFixedSection)
    (canonical : PackedFixedSectionCanonical packed) :
    StoredFixedFieldViewExact (packedFixedFieldView packed canonical)
      (decodedPackedFields packed canonical) := by
  constructor <;> intros <;> rfl

theorem packedFixedMessagesMatch_constructs_exact_decode_and_view
    {tape : DeployedFixedTape} {packed : PackedFixedSection}
    {stored : FixedFieldView QM31Exact}
    (messages : PackedFixedMessagesMatch tape packed)
    (canonical : PackedFixedSectionCanonical packed)
    (storedExact : StoredFixedFieldViewExact stored
      (decodedPackedFields packed canonical)) :
    ∃ decoded : Fin 641 → QM31Exact,
      FixedFieldDecodeExact (rawOfMessages tape.messages) decoded ∧
      stored = decodedFixedFieldView decoded := by
  refine ⟨decodedPackedFields packed canonical, ?_, ?_⟩
  · exact tapeCarriesDecodedFixedFields_fixedFieldDecodeExact
      (packedFixedMessagesMatch_tapeCarriesDecodedFixedFields
        messages canonical)
  · exact storedFixedFieldViewExact_eq_decodedFixedFieldView storedExact

#print axioms fixed_limb_count_exact
#print axioms fixed_field_partition_exact
#print axioms fixed_meaningful_bits_exact
#print axioms fixed_packed_bytes_exact
#print axioms fixed_padding_bits_exact
#print axioms v7_query_bytes_exact
#print axioms v7_query_section_bytes_exact
#print axioms v7_fixed_and_following_offsets_exact
#print axioms v7_exact_body_length_with_frontiers
#print axioms v7_maximum_body_length_exact
#print axioms fixed_last_limb_exact_range
#print axioms fixedLimbBitStart_within_meaningful
#print axioms fixedLimbBitStart_byte_decomposition
#print axioms fixedLimbFiveByteWindow_within_packed
#print axioms fixedLimbIndex_inverse
#print axioms fieldAtLimbOrdinal_fixedLimbIndex
#print axioms limbAtLimbOrdinal_fixedLimbIndex
#print axioms fixedLimbBitStart_at_ordinal
#print axioms reader_state_eight_limb_cycle
#print axioms reader_next_byte_count_eight_limb_cycle
#print axioms reader_state_full_cycle_advance
#print axioms reader_state_after_320_full_cycles
#print axioms reader_state_after_all_fixed_limbs
#print axioms reader_final_four_limb_byte_span
#print axioms packedSectionByte_eq
#print axioms packedLimbNat_lt_two_pow_31
#print axioms packedFixedSectionCanonical_of_every_ordinal
#print axioms packedFixedPaddingZero_iff_canonicalFixedPadding
#print axioms rawFixedFieldBytes_rawWithPackedFixedFields
#print axioms rawOfMessages_messagesWithPackedFixedFields
#print axioms tapeWithPackedFixedFields_messages_match
#print axioms packedFieldMessageBytes_eq_encodeTagQM31ExactLE
#print axioms rawWithPackedFixedFields_fixedFieldDecodeExact
#print axioms exactCanonicalPackedSection_constructs_raw_decode_and_view
#print axioms packedFixedMessagesMatch_tapeCarriesDecodedFixedFields
#print axioms tapeCarriesDecodedFixedFields_fixedFieldDecodeExact
#print axioms tapeCarriesDecodedFixedFields_constructs_exact_decode
#print axioms packedFixedMessagesMatch_constructs_exact_decode
#print axioms tapeWithPackedFixedFields_constructs_exact_decode
#print axioms exactCanonicalPackedSection_constructs_projected_decode_and_view
#print axioms packedFixedMessagesMatch_constructs_exact_decode_and_canonical_view
#print axioms storedFixedFieldViewExact_eq_decodedFixedFieldView
#print axioms packedFixedFieldView_storedFixedFieldViewExact
#print axioms packedFixedMessagesMatch_constructs_exact_decode_and_view

end AspisV7Tag73FixedFieldLayoutModel
