import AspisFormal.V5ComponentCDownstreamDeployed

/-!
# v5 freeze audit: complete runtime wire view

This file models the byte layout accepted by the feature-gated mode-9 CU
fixture.  It uses the direct Component-C downstream map and its runtime-sized
deduplicated later layers.  It deliberately does not identify this fixture with
a production grammar.

The fixed account prefix is 27,200 bytes.  Five Merkle sections follow it.  A
section contains a two-byte record count, salted records, a four-byte frontier
count, and the frontier hashes.  The three later record counts are runtime
deduplicated counts, rather than frozen arrays of length eighteen.

The classification has the six cases requested by the freeze audit.  It is
total and single-valued, but it is not a coverage theorem: the accepted fixture
contains an 8,064-byte legacy production-C1 diagnostic span beginning at byte
24.  The mode-9 authentication path does not compare that span with an
authenticated opening.  The query selector at byte 27,199 is also uncovered:
the current fixture writes zero, while the accepted parser permits three
values.  Commitment roots and Merkle frontier hashes stay outside the
algebraic A/B/direct-C hiding theorems until a named computational view
assumption is supplied.
-/

namespace AspisV5FreezeCompleteWireView

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCDownstreamDeployed

/-! ## Exact constants copied from the runtime parser layout -/

def realPrefixBytes : Nat := 6423
def fixedAccountBytes : Nat := 27200
def queryCount : Nat := 18
def leafSaltBytes : Nat := 32
def hashBytes : Nat := 32
def c1ValueBytes : Nat := 256
def c2ValueBytes : Nat := 192
def laterValueBytes : Nat := 64
def relationTailBytes : Nat := 928
def sealedProofHeaderBytes : Nat := 40
def fullTransactionInstructionBytes : Nat := 169

theorem fixed_constants_exact :
    realPrefixBytes = 6423 ∧ fixedAccountBytes = 27200 ∧
    queryCount = 18 ∧ leafSaltBytes = 32 ∧ hashBytes = 32 ∧
    c1ValueBytes = 256 ∧ c2ValueBytes = 192 ∧
    laterValueBytes = 64 ∧ relationTailBytes = 928 ∧
    sealedProofHeaderBytes = 40 ∧ fullTransactionInstructionBytes = 169 := by
  norm_num [realPrefixBytes, fixedAccountBytes, queryCount, leafSaltBytes,
    hashBytes, c1ValueBytes, c2ValueBytes, laterValueBytes, relationTailBytes,
    sealedProofHeaderBytes, fullTransactionInstructionBytes]

/-! ## Public tag-67 instruction and sealed proof-account header -/

inductive InstructionSegment
  | tag
  | currentAnchor
  | nullifier
  | outputCommitment
  | outputAnchor
  | assetId
  | fee
  | deploymentDomain
  deriving DecidableEq, Fintype

def instructionSegmentBytes : InstructionSegment → Nat
  | .tag => 1
  | .currentAnchor | .nullifier | .outputCommitment | .outputAnchor => 32
  | .assetId | .fee => 4
  | .deploymentDomain => 32

def instructionSegmentStart : InstructionSegment → Nat
  | .tag => 0
  | .currentAnchor => 1
  | .nullifier => 33
  | .outputCommitment => 65
  | .outputAnchor => 97
  | .assetId => 129
  | .fee => 133
  | .deploymentDomain => 137

abbrev InstructionByte :=
  (field : InstructionSegment) × Fin (instructionSegmentBytes field)

inductive SealedHeaderSegment
  | magic
  | proofLength
  | zeroUploadAuthority
  deriving DecidableEq, Fintype

def sealedHeaderSegmentBytes : SealedHeaderSegment → Nat
  | .magic => 4
  | .proofLength => 4
  | .zeroUploadAuthority => 32

def sealedHeaderSegmentStart : SealedHeaderSegment → Nat
  | .magic => 0
  | .proofLength => 4
  | .zeroUploadAuthority => 8

abbrev SealedHeaderByte :=
  (field : SealedHeaderSegment) × Fin (sealedHeaderSegmentBytes field)

theorem public_wrapper_offsets_exact :
    instructionSegmentStart .tag = 0 ∧
    instructionSegmentStart .currentAnchor = 1 ∧
    instructionSegmentStart .nullifier = 33 ∧
    instructionSegmentStart .outputCommitment = 65 ∧
    instructionSegmentStart .outputAnchor = 97 ∧
    instructionSegmentStart .assetId = 129 ∧
    instructionSegmentStart .fee = 133 ∧
    instructionSegmentStart .deploymentDomain = 137 ∧
    instructionSegmentStart .deploymentDomain +
        instructionSegmentBytes .deploymentDomain = fullTransactionInstructionBytes ∧
    sealedHeaderSegmentStart .magic = 0 ∧
    sealedHeaderSegmentStart .proofLength = 4 ∧
    sealedHeaderSegmentStart .zeroUploadAuthority = 8 ∧
    sealedHeaderSegmentStart .zeroUploadAuthority +
        sealedHeaderSegmentBytes .zeroUploadAuthority = sealedProofHeaderBytes := by
  norm_num [instructionSegmentStart, instructionSegmentBytes,
    fullTransactionInstructionBytes, sealedHeaderSegmentStart,
    sealedHeaderSegmentBytes, sealedProofHeaderBytes]

/-! ## Every byte of the 27,200-byte fixed account prefix -/

inductive FixedSegment
  | accountMagic
  | gamma
  | legacyProductionC1
  | candidateC1Duplicate
  | c2Duplicate
  | relationScales
  | relationPoints
  | relationClaimsDuplicate
  | relationAlphas
  | relationFoldNoncesAndZeroPad
  | prefixHeader
  | prefixC1Root
  | prefixC2Root
  | prefixInitialBClaim
  | prefixBSumcheck
  | prefixPointClaims
  | prefixTerminalReal
  | prefixTerminalMask
  | prefixTerminalMasked
  | prefixInactiveClaim
  | prefixPublicFsSalts
  | prefixZeroReserve
  | atomicTerminalContext
  | privateRoots
  | finalCoefficientsDuplicate
  | relationChallengePoints
  | relationOodValues
  | relationOodMixes
  | relationSumcheckRows
  | relationFinalCoefficients
  | finalGrindingNonce
  | querySelector
  deriving DecidableEq, Fintype

def fixedSegmentBytes : FixedSegment → Nat
  | .accountMagic => 8
  | .gamma => 16
  | .legacyProductionC1 => 8064
  | .candidateC1Duplicate => 5184
  | .c2Duplicate => 4032
  | .relationScales => 48
  | .relationPoints => 480
  | .relationClaimsDuplicate => 1216
  | .relationAlphas => 64
  | .relationFoldNoncesAndZeroPad => 64
  | .prefixHeader => 23
  | .prefixC1Root => 32
  | .prefixC2Root => 32
  | .prefixInitialBClaim => 16
  | .prefixBSumcheck => 4480
  | .prefixPointClaims => 1216
  | .prefixTerminalReal => 16
  | .prefixTerminalMask => 16
  | .prefixTerminalMasked => 16
  | .prefixInactiveClaim => 16
  | .prefixPublicFsSalts => 160
  | .prefixZeroReserve => 400
  | .atomicTerminalContext => 440
  | .privateRoots => 160
  | .finalCoefficientsDuplicate => 64
  | .relationChallengePoints => 160
  | .relationOodValues => 128
  | .relationOodMixes => 128
  | .relationSumcheckRows => 448
  | .relationFinalCoefficients => 64
  | .finalGrindingNonce => 8
  | .querySelector => 1

def fixedSegmentStart : FixedSegment → Nat
  | .accountMagic => 0
  | .gamma => 8
  | .legacyProductionC1 => 24
  | .candidateC1Duplicate => 8088
  | .c2Duplicate => 13272
  | .relationScales => 17304
  | .relationPoints => 17352
  | .relationClaimsDuplicate => 17832
  | .relationAlphas => 19048
  | .relationFoldNoncesAndZeroPad => 19112
  | .prefixHeader => 19176
  | .prefixC1Root => 19199
  | .prefixC2Root => 19231
  | .prefixInitialBClaim => 19263
  | .prefixBSumcheck => 19279
  | .prefixPointClaims => 23759
  | .prefixTerminalReal => 24975
  | .prefixTerminalMask => 24991
  | .prefixTerminalMasked => 25007
  | .prefixInactiveClaim => 25023
  | .prefixPublicFsSalts => 25039
  | .prefixZeroReserve => 25199
  | .atomicTerminalContext => 25599
  | .privateRoots => 26039
  | .finalCoefficientsDuplicate => 26199
  | .relationChallengePoints => 26263
  | .relationOodValues => 26423
  | .relationOodMixes => 26551
  | .relationSumcheckRows => 26679
  | .relationFinalCoefficients => 27127
  | .finalGrindingNonce => 27191
  | .querySelector => 27199

abbrev FixedByte := (segment : FixedSegment) × Fin (fixedSegmentBytes segment)

def fixedByteOffset (coordinate : FixedByte) : Nat :=
  fixedSegmentStart coordinate.1 + coordinate.2.val

theorem fixed_segment_offsets_exact :
    fixedSegmentStart .accountMagic = 0 ∧
    fixedSegmentStart .gamma = 8 ∧
    fixedSegmentStart .legacyProductionC1 = 24 ∧
    fixedSegmentStart .candidateC1Duplicate = 8088 ∧
    fixedSegmentStart .c2Duplicate = 13272 ∧
    fixedSegmentStart .relationScales = 17304 ∧
    fixedSegmentStart .relationPoints = 17352 ∧
    fixedSegmentStart .relationClaimsDuplicate = 17832 ∧
    fixedSegmentStart .relationAlphas = 19048 ∧
    fixedSegmentStart .relationFoldNoncesAndZeroPad = 19112 ∧
    fixedSegmentStart .prefixHeader = 19176 ∧
    fixedSegmentStart .prefixC1Root = 19199 ∧
    fixedSegmentStart .prefixC2Root = 19231 ∧
    fixedSegmentStart .prefixInitialBClaim = 19263 ∧
    fixedSegmentStart .prefixBSumcheck = 19279 ∧
    fixedSegmentStart .prefixPointClaims = 23759 ∧
    fixedSegmentStart .prefixTerminalReal = 24975 ∧
    fixedSegmentStart .prefixTerminalMask = 24991 ∧
    fixedSegmentStart .prefixTerminalMasked = 25007 ∧
    fixedSegmentStart .prefixInactiveClaim = 25023 ∧
    fixedSegmentStart .prefixPublicFsSalts = 25039 ∧
    fixedSegmentStart .prefixZeroReserve = 25199 ∧
    fixedSegmentStart .atomicTerminalContext = 25599 ∧
    fixedSegmentStart .privateRoots = 26039 ∧
    fixedSegmentStart .finalCoefficientsDuplicate = 26199 ∧
    fixedSegmentStart .relationChallengePoints = 26263 ∧
    fixedSegmentStart .relationOodValues = 26423 ∧
    fixedSegmentStart .relationOodMixes = 26551 ∧
    fixedSegmentStart .relationSumcheckRows = 26679 ∧
    fixedSegmentStart .relationFinalCoefficients = 27127 ∧
    fixedSegmentStart .finalGrindingNonce = 27191 ∧
    fixedSegmentStart .querySelector = 27199 := by
  norm_num [fixedSegmentStart]

theorem fixed_segment_ends_within_account (segment : FixedSegment) :
    fixedSegmentStart segment + fixedSegmentBytes segment ≤ fixedAccountBytes := by
  cases segment <;> norm_num [fixedSegmentStart, fixedSegmentBytes, fixedAccountBytes]

theorem fixed_byte_offset_lt (coordinate : FixedByte) :
    fixedByteOffset coordinate < fixedAccountBytes := by
  have hend := fixed_segment_ends_within_account coordinate.1
  have hlocal := coordinate.2.isLt
  simp only [fixedByteOffset]
  omega

theorem fixed_layout_ends_exactly :
    fixedSegmentStart .querySelector + fixedSegmentBytes .querySelector =
      fixedAccountBytes := by
  rfl

/-! ## The five runtime-sized Merkle sections -/

inductive OpeningSection
  | c1
  | c2
  | later1
  | later2
  | later3
  deriving DecidableEq, Fintype

def openingRecordCount (later1Count later2Count later3Count : Nat) :
    OpeningSection → Nat
  | .c1 => queryCount
  | .c2 => queryCount
  | .later1 => later1Count
  | .later2 => later2Count
  | .later3 => later3Count

def openingRecordValueBytes : OpeningSection → Nat
  | .c1 => c1ValueBytes
  | .c2 => c2ValueBytes
  | .later1 | .later2 | .later3 => laterValueBytes

def openingFrontierCount
    (c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :
    OpeningSection → Nat
  | .c1 => c1Frontier
  | .c2 => c2Frontier
  | .later1 => later1Frontier
  | .later2 => later2Frontier
  | .later3 => later3Frontier

def openingSectionBytes
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat)
    (opening : OpeningSection) : Nat :=
  2 + openingRecordCount later1Count later2Count later3Count opening *
      (openingRecordValueBytes opening + leafSaltBytes) +
    4 + openingFrontierCount c1Frontier c2Frontier later1Frontier
      later2Frontier later3Frontier opening * hashBytes

def openingRelativeStart
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :
    OpeningSection → Nat
  | .c1 => 0
  | .c2 => openingSectionBytes later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .c1
  | .later1 =>
      openingSectionBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .c1 +
      openingSectionBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .c2
  | .later2 =>
      openingSectionBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .c1 +
      openingSectionBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .c2 +
      openingSectionBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .later1
  | .later3 =>
      openingSectionBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .c1 +
      openingSectionBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .c2 +
      openingSectionBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .later1 +
      openingSectionBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .later2

def privateOpeningBytes
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) : Nat :=
  30 + 18 * (288 + 224) + 96 * (later1Count + later2Count + later3Count) +
    32 * (c1Frontier + c2Frontier + later1Frontier + later2Frontier + later3Frontier)

def runtimeWireBytes
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) : Nat :=
  fixedAccountBytes + privateOpeningBytes later1Count later2Count later3Count
    c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier

abbrev OpeningByte
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :=
  (opening : OpeningSection) ×
    Fin (openingSectionBytes later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier opening)

abbrev CandidateWireByte
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :=
  FixedByte ⊕ OpeningByte later1Count later2Count later3Count
    c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier

abbrev RuntimeWireByte
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :=
  Fin (runtimeWireBytes later1Count later2Count later3Count
    c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier)

def sealedProofAccountBytes
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) : Nat :=
  sealedProofHeaderBytes + runtimeWireBytes later1Count later2Count later3Count
    c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier

def completeReleasedBytes
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) : Nat :=
  fullTransactionInstructionBytes + sealedProofAccountBytes later1Count later2Count later3Count
    c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier

abbrev CompleteReleasedByte
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :=
  InstructionByte ⊕
    (SealedHeaderByte ⊕ CandidateWireByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier)

abbrev CompleteRuntimeByte
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :=
  Fin (completeReleasedBytes later1Count later2Count later3Count
    c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier)

def openingByteOffset
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat}
    (coordinate : OpeningByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier) : Nat :=
  fixedAccountBytes +
    openingRelativeStart later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier coordinate.1 +
    coordinate.2.val

def candidateByteOffset
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat} :
    CandidateWireByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier → Nat
  | .inl coordinate => fixedByteOffset coordinate
  | .inr coordinate => openingByteOffset coordinate

def instructionByteOffset (coordinate : InstructionByte) : Nat :=
  instructionSegmentStart coordinate.1 + coordinate.2.val

def sealedHeaderByteOffset (coordinate : SealedHeaderByte) : Nat :=
  instructionSegmentStart .deploymentDomain + instructionSegmentBytes .deploymentDomain +
    sealedHeaderSegmentStart coordinate.1 + coordinate.2.val

def completeByteOffset
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat} :
    CompleteReleasedByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier → Nat
  | .inl coordinate => instructionByteOffset coordinate
  | .inr (.inl coordinate) => sealedHeaderByteOffset coordinate
  | .inr (.inr coordinate) =>
      fullTransactionInstructionBytes + sealedProofHeaderBytes + candidateByteOffset coordinate

theorem private_opening_bytes_eq_ordered_section_sum
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :
    privateOpeningBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier =
      openingSectionBytes later1Count later2Count later3Count
          c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .c1 +
        openingSectionBytes later1Count later2Count later3Count
          c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .c2 +
        openingSectionBytes later1Count later2Count later3Count
          c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .later1 +
        openingSectionBytes later1Count later2Count later3Count
          c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .later2 +
        openingSectionBytes later1Count later2Count later3Count
          c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier .later3 := by
  simp [privateOpeningBytes, openingSectionBytes, openingRecordCount,
    openingRecordValueBytes, openingFrontierCount, queryCount, c1ValueBytes,
    c2ValueBytes, laterValueBytes, leafSaltBytes, hashBytes]
  ring

theorem runtime_wire_byte_count
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :
    Fintype.card (RuntimeWireByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier) =
      runtimeWireBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier := by
  exact Fintype.card_fin _

theorem complete_runtime_byte_count
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :
    Fintype.card (CompleteRuntimeByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier) =
      completeReleasedBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier := by
  exact Fintype.card_fin _

theorem current_recorded_section_sizes :
    openingSectionBytes 18 18 18 326 326 272 218 164 .c1 = 15622 ∧
    openingSectionBytes 18 18 18 326 326 272 218 164 .c2 = 14470 ∧
    openingSectionBytes 18 18 18 326 326 272 218 164 .later1 = 10438 ∧
    openingSectionBytes 18 18 18 326 326 272 218 164 .later2 = 8710 ∧
    openingSectionBytes 18 18 18 326 326 272 218 164 .later3 = 6982 := by
  norm_num [openingSectionBytes, openingRecordCount, openingRecordValueBytes,
    openingFrontierCount, queryCount, c1ValueBytes, c2ValueBytes,
    laterValueBytes, leafSaltBytes, hashBytes]

theorem current_recorded_wire_bytes :
    privateOpeningBytes 18 18 18 326 326 272 218 164 = 56222 ∧
    runtimeWireBytes 18 18 18 326 326 272 218 164 = 83422 ∧
    sealedProofAccountBytes 18 18 18 326 326 272 218 164 = 83462 ∧
    completeReleasedBytes 18 18 18 326 326 272 218 164 = 83631 := by
  norm_num [privateOpeningBytes, runtimeWireBytes, fixedAccountBytes,
    sealedProofAccountBytes, sealedProofHeaderBytes, completeReleasedBytes,
    fullTransactionInstructionBytes]

/-! ## Total six-way classification -/

inductive CoverageClass
  | publicWitnessIndependent
  | hiddenByA
  | hiddenByCorrelatedB
  | hiddenByDirectC
  | determinedByAuthenticatedIdentity
  | currentlyUncovered
  deriving DecidableEq, Fintype

def pointClaimClass (_point lane : Nat) : CoverageClass :=
  if lane ≤ 16 then
    .hiddenByA
  else if lane = 17 then
    .hiddenByCorrelatedB
  else
    .hiddenByDirectC

def fixedByteClass (coordinate : FixedByte) : CoverageClass :=
  match coordinate.1 with
  | .accountMagic => .publicWitnessIndependent
  | .gamma => .determinedByAuthenticatedIdentity
  | .legacyProductionC1 => .currentlyUncovered
  | .candidateC1Duplicate => .determinedByAuthenticatedIdentity
  | .c2Duplicate => .determinedByAuthenticatedIdentity
  | .relationScales => .determinedByAuthenticatedIdentity
  | .relationPoints => .determinedByAuthenticatedIdentity
  | .relationClaimsDuplicate => .determinedByAuthenticatedIdentity
  | .relationAlphas => .determinedByAuthenticatedIdentity
  | .relationFoldNoncesAndZeroPad => .determinedByAuthenticatedIdentity
  | .prefixHeader => .publicWitnessIndependent
  | .prefixC1Root => .currentlyUncovered
  | .prefixC2Root => .currentlyUncovered
  | .prefixInitialBClaim => .hiddenByCorrelatedB
  | .prefixBSumcheck => .hiddenByCorrelatedB
  | .prefixPointClaims =>
      pointClaimClass ((coordinate.2.val / 16) / 19) ((coordinate.2.val / 16) % 19)
  | .prefixTerminalReal => .determinedByAuthenticatedIdentity
  | .prefixTerminalMask => .determinedByAuthenticatedIdentity
  | .prefixTerminalMasked => .determinedByAuthenticatedIdentity
  | .prefixInactiveClaim => .hiddenByCorrelatedB
  | .prefixPublicFsSalts => .publicWitnessIndependent
  | .prefixZeroReserve => .publicWitnessIndependent
  | .atomicTerminalContext => .determinedByAuthenticatedIdentity
  | .privateRoots =>
      if coordinate.2.val < 64 then
        .determinedByAuthenticatedIdentity
      else
        .currentlyUncovered
  | .finalCoefficientsDuplicate => .determinedByAuthenticatedIdentity
  | .relationChallengePoints => .determinedByAuthenticatedIdentity
  | .relationOodValues => .hiddenByDirectC
  | .relationOodMixes => .determinedByAuthenticatedIdentity
  | .relationSumcheckRows => .hiddenByDirectC
  | .relationFinalCoefficients => .hiddenByDirectC
  | .finalGrindingNonce => .determinedByAuthenticatedIdentity
  | .querySelector => .currentlyUncovered

def openingByteClass
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat}
    (coordinate : OpeningByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier) : CoverageClass :=
  let opening := coordinate.1
  let offset := coordinate.2.val
  let count := openingRecordCount later1Count later2Count later3Count opening
  let valueBytes := openingRecordValueBytes opening
  let recordBytes := valueBytes + leafSaltBytes
  let recordsBytes := count * recordBytes
  if offset < 2 then
    .determinedByAuthenticatedIdentity
  else if offset < 2 + recordsBytes then
    let inRecord := (offset - 2) % recordBytes
    if inRecord < valueBytes then
      match opening with
      | .c1 => .hiddenByA
      | .c2 =>
          if inRecord / 64 = 0 then .hiddenByA
          else if inRecord / 64 = 1 then .hiddenByCorrelatedB
          else .hiddenByDirectC
      | .later1 | .later2 | .later3 => .hiddenByDirectC
    else
      .publicWitnessIndependent
  else if offset < 2 + recordsBytes + 4 then
    .determinedByAuthenticatedIdentity
  else
    .currentlyUncovered

def candidateByteClass
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat} :
    CandidateWireByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier → CoverageClass
  | .inl coordinate => fixedByteClass coordinate
  | .inr coordinate => openingByteClass coordinate

def completeByteClass
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat} :
    CompleteReleasedByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier → CoverageClass
  | .inl _ => .publicWitnessIndependent
  | .inr (.inl _) => .publicWitnessIndependent
  | .inr (.inr coordinate) => candidateByteClass coordinate

def ClassifiedAs
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat}
    (coordinate : CandidateWireByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier)
    (classification : CoverageClass) : Prop :=
  candidateByteClass coordinate = classification

theorem every_byte_has_exactly_one_class
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat}
    (coordinate : CandidateWireByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier) :
    ∃! classification, ClassifiedAs coordinate classification := by
  refine ⟨candidateByteClass coordinate, rfl, ?_⟩
  intro classification hclassification
  exact hclassification.symm

theorem every_complete_released_byte_has_exactly_one_class
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat}
    (coordinate : CompleteReleasedByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier) :
    ∃! classification, completeByteClass coordinate = classification := by
  refine ⟨completeByteClass coordinate, rfl, ?_⟩
  intro classification hclassification
  exact hclassification.symm

theorem no_byte_has_two_distinct_classes
    {later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat}
    (coordinate : CandidateWireByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier)
    {left right : CoverageClass}
    (hleft : ClassifiedAs coordinate left)
    (hright : ClassifiedAs coordinate right) : left = right := by
  exact hleft.symm.trans hright

def FullyCovered
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) : Prop :=
  ∀ coordinate : CandidateWireByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier,
    candidateByteClass coordinate ≠ .currentlyUncovered

def firstLegacyProductionC1Byte : FixedByte :=
  ⟨.legacyProductionC1, ⟨0, by norm_num [fixedSegmentBytes]⟩⟩

def querySelectorByte : FixedByte :=
  ⟨.querySelector, ⟨0, by norm_num [fixedSegmentBytes]⟩⟩

theorem legacy_production_c1_first_byte_is_uncovered :
    fixedByteOffset firstLegacyProductionC1Byte = 24 ∧
    fixedByteClass firstLegacyProductionC1Byte = .currentlyUncovered := by
  constructor <;> rfl

theorem legacy_production_c1_absolute_offsets :
    sealedProofHeaderBytes + fixedByteOffset firstLegacyProductionC1Byte = 64 ∧
    fullTransactionInstructionBytes + sealedProofHeaderBytes +
        fixedByteOffset firstLegacyProductionC1Byte = 233 := by
  rw [legacy_production_c1_first_byte_is_uncovered.1]
  norm_num [sealedProofHeaderBytes, fullTransactionInstructionBytes]

theorem accepted_query_selector_is_uncovered :
    fixedByteOffset querySelectorByte = 27199 ∧
    fixedByteClass querySelectorByte = .currentlyUncovered := by
  constructor <;> rfl

theorem accepted_runtime_view_is_not_fully_covered
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :
    ¬ FullyCovered later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier := by
  intro hcovered
  exact hcovered (.inl firstLegacyProductionC1Byte) rfl

def CompleteReleasedViewFullyCovered
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) : Prop :=
  ∀ coordinate : CompleteReleasedByte later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier,
    completeByteClass coordinate ≠ .currentlyUncovered

theorem complete_released_view_is_not_fully_covered
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :
    ¬ CompleteReleasedViewFullyCovered later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier := by
  intro hcovered
  exact hcovered (.inr (.inr (.inl firstLegacyProductionC1Byte))) rfl

/-! ## Adversarial layout teeth -/

def prefixClaimPointMajorOffset (point lane byte : Nat) : Nat :=
  23759 + 16 * (19 * point + lane) + byte

def prefixClaimLaneMajorOffset (point lane byte : Nat) : Nat :=
  23759 + 16 * (4 * lane + point) + byte

theorem point_major_is_not_lane_major :
    prefixClaimPointMajorOffset 1 0 0 = 24063 ∧
    prefixClaimLaneMajorOffset 1 0 0 = 23775 ∧
    prefixClaimPointMajorOffset 1 0 0 ≠ prefixClaimLaneMajorOffset 1 0 0 := by
  norm_num [prefixClaimPointMajorOffset, prefixClaimLaneMajorOffset]

theorem swapping_b_and_c_claim_lanes_changes_wire :
    prefixClaimPointMajorOffset 0 17 0 = 24031 ∧
    prefixClaimPointMajorOffset 0 18 0 = 24047 ∧
    prefixClaimPointMajorOffset 0 17 0 ≠ prefixClaimPointMajorOffset 0 18 0 := by
  norm_num [prefixClaimPointMajorOffset]

def candidateC1SlotMajorOffset (slot lane byte : Nat) : Nat :=
  8088 + (16 * slot + lane) * 4 + byte

def candidateC1LaneMajorOffset (slot lane byte : Nat) : Nat :=
  8088 + (4 * lane + slot) * 4 + byte

theorem c1_slot_order_transposition_changes_wire :
    candidateC1SlotMajorOffset 1 0 0 = 8152 ∧
    candidateC1LaneMajorOffset 1 0 0 = 8092 ∧
    candidateC1SlotMajorOffset 1 0 0 ≠ candidateC1LaneMajorOffset 1 0 0 := by
  norm_num [candidateC1SlotMajorOffset, candidateC1LaneMajorOffset]

def runtimeDirectCReleasedRows (later1Count later2Count later3Count : Nat) : Nat :=
  40 + 4 * (later1Count + later2Count + later3Count)

theorem runtime_direct_c_rows_agree_with_deployed_map
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (schedule : DeployedRuntimeSchedule F K) :
    fRows (decodeFriSchedule schedule) =
      runtimeDirectCReleasedRows schedule.later1Count schedule.later2Count
        schedule.later3Count := by
  exact deployed_output_dimension schedule

theorem frozen_256_iff_runtime_later_count_sum
    (later1Count later2Count later3Count : Nat) :
    runtimeDirectCReleasedRows later1Count later2Count later3Count = 256 ↔
      later1Count + later2Count + later3Count = 54 := by
  simp only [runtimeDirectCReleasedRows]
  omega

theorem frozen_256_is_not_the_runtime_deduplicated_shape :
    runtimeDirectCReleasedRows 18 18 18 = 256 ∧
    runtimeDirectCReleasedRows 4 3 2 = 76 ∧
    runtimeDirectCReleasedRows 4 3 2 ≠ 256 := by
  norm_num [runtimeDirectCReleasedRows]

theorem one_byte_truncation_changes_exact_length
    (later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier : Nat) :
    runtimeWireBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier - 1 ≠
      runtimeWireBytes later1Count later2Count later3Count
        c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier := by
  have hpositive : 0 < runtimeWireBytes later1Count later2Count later3Count
      c1Frontier c2Frontier later1Frontier later2Frontier later3Frontier := by
    simp [runtimeWireBytes, fixedAccountBytes]
  omega

def realPrefixWithoutOneTerminalCoordinateBytes : Nat := realPrefixBytes - 16

theorem omitted_terminal_coordinate_changes_prefix_length :
    realPrefixWithoutOneTerminalCoordinateBytes = 6407 ∧
    realPrefixWithoutOneTerminalCoordinateBytes ≠ realPrefixBytes := by
  norm_num [realPrefixWithoutOneTerminalCoordinateBytes, realPrefixBytes]

inductive BTerminalRelease
  | fourthPointClaim
  | terminalRealIdentity
  | terminalMaskIdentity
  | terminalMaskedIdentity
  deriving DecidableEq, Fintype

def bTerminalReleaseClass : BTerminalRelease → CoverageClass
  | .fourthPointClaim => .hiddenByCorrelatedB
  | .terminalRealIdentity | .terminalMaskIdentity | .terminalMaskedIdentity =>
      .determinedByAuthenticatedIdentity

def IsIndependentMaskClass : CoverageClass → Prop
  | .hiddenByA | .hiddenByCorrelatedB | .hiddenByDirectC => True
  | _ => False

theorem b_terminal_identity_is_not_masked_twice :
    bTerminalReleaseClass .fourthPointClaim = .hiddenByCorrelatedB ∧
    bTerminalReleaseClass .terminalRealIdentity = .determinedByAuthenticatedIdentity ∧
    bTerminalReleaseClass .terminalMaskIdentity = .determinedByAuthenticatedIdentity ∧
    bTerminalReleaseClass .terminalMaskedIdentity = .determinedByAuthenticatedIdentity ∧
    ¬ IsIndependentMaskClass (bTerminalReleaseClass .terminalRealIdentity) ∧
    ¬ IsIndependentMaskClass (bTerminalReleaseClass .terminalMaskIdentity) ∧
    ¬ IsIndependentMaskClass (bTerminalReleaseClass .terminalMaskedIdentity) := by
  exact ⟨rfl, rfl, rfl, rfl, id, id, id⟩

/-! ## Named executable-correspondence boundaries -/

def ExactRustSerializerParserCorrespondence
    {State Bytes Parsed : Type*}
    (rustSerializer modelSerializer : State → Bytes)
    (rustParser modelParser : Bytes → Parsed) : Prop :=
  rustSerializer = modelSerializer ∧ rustParser = modelParser

def ExactRustTranscriptOrderCorrespondence
    {State Challenge : Type*}
    (rustChallenges modelChallenges : State → Challenge) : Prop :=
  rustChallenges = modelChallenges

/-!
The two predicates above are premises for an executable audit, not conclusions
of this file.  Likewise, computational hiding/binding for the roots and
frontier hashes and entropy for all public and leaf salts remain named external
assumptions.  The negative coverage theorem is independent of those premises:
the legacy span is accepted fixture data outside the mode-9 authentication
comparison.
-/

#print axioms fixed_constants_exact
#print axioms public_wrapper_offsets_exact
#print axioms fixed_segment_offsets_exact
#print axioms fixed_segment_ends_within_account
#print axioms fixed_byte_offset_lt
#print axioms fixed_layout_ends_exactly
#print axioms private_opening_bytes_eq_ordered_section_sum
#print axioms runtime_wire_byte_count
#print axioms complete_runtime_byte_count
#print axioms current_recorded_section_sizes
#print axioms current_recorded_wire_bytes
#print axioms every_byte_has_exactly_one_class
#print axioms every_complete_released_byte_has_exactly_one_class
#print axioms no_byte_has_two_distinct_classes
#print axioms legacy_production_c1_first_byte_is_uncovered
#print axioms legacy_production_c1_absolute_offsets
#print axioms accepted_query_selector_is_uncovered
#print axioms accepted_runtime_view_is_not_fully_covered
#print axioms complete_released_view_is_not_fully_covered
#print axioms point_major_is_not_lane_major
#print axioms swapping_b_and_c_claim_lanes_changes_wire
#print axioms c1_slot_order_transposition_changes_wire
#print axioms runtime_direct_c_rows_agree_with_deployed_map
#print axioms frozen_256_iff_runtime_later_count_sum
#print axioms frozen_256_is_not_the_runtime_deduplicated_shape
#print axioms one_byte_truncation_changes_exact_length
#print axioms omitted_terminal_coordinate_changes_prefix_length
#print axioms b_terminal_identity_is_not_masked_twice

end AspisV5FreezeCompleteWireView
