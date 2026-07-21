import AspisFormal.V5ExactRuntimeWireRepair
import AspisFormal.V5ComponentCDownstreamDeployed
import AspisFormal.V5SelectedGoodVerifierRelation

/-!
# Exact semantic inventory for the repaired v5 runtime wire

This file refines the byte partition in `V5ExactRuntimeWireRepair` into the
semantic fields accepted by the feature-gated mode-9 parser.  The fixed body
is exactly 19,136 bytes and is followed by the five runtime-sized private
opening sections.  The retired 8,064-byte width-26 C1 span has no constructor
in this inventory.

The classification is intentionally an obligation ledger rather than a new
cryptographic theorem.  In particular, commitment roots and Merkle frontier
hashes receive their own computational class, and the selector receives its
own honest-prover class.  The selected-good verifier relation alone does not
make an adversarially chosen selector witness-independent.  Component-A,
correlated-B, direct-C, computational PCS/Merkle, entropy, Fiat--Shamir, and
Rust-to-Lean correspondence obligations therefore remain explicit.
-/

namespace AspisFormal.V5RepairedRuntimeWireClassification

open V5ExactRuntimeWireRepair
open AspisV5ComponentCDownstreamDeployed
open AspisV5ComponentCConcreteFoldLinearity

/-! ## Fine-grained fixed-prefix inventory -/

inductive FixedSemanticSegment where
  | accountMagic
  | gamma
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
  | privateC1RootDuplicate
  | privateC2RootDuplicate
  | privateLaterRoots
  | finalCoefficientsDuplicate
  | relationChallengePoints
  | relationOodValues
  | relationOodMixes
  | relationSumcheckRows
  | relationFinalCoefficients
  | finalGrindingNonce
  | querySelector
  deriving DecidableEq, Fintype

def FixedSemanticSegment.start : FixedSemanticSegment → Nat
  | .accountMagic => 0
  | .gamma => 8
  | .candidateC1Duplicate => 24
  | .c2Duplicate => 5208
  | .relationScales => 9240
  | .relationPoints => 9288
  | .relationClaimsDuplicate => 9768
  | .relationAlphas => 10984
  | .relationFoldNoncesAndZeroPad => 11048
  | .prefixHeader => 11112
  | .prefixC1Root => 11135
  | .prefixC2Root => 11167
  | .prefixInitialBClaim => 11199
  | .prefixBSumcheck => 11215
  | .prefixPointClaims => 15695
  | .prefixTerminalReal => 16911
  | .prefixTerminalMask => 16927
  | .prefixTerminalMasked => 16943
  | .prefixInactiveClaim => 16959
  | .prefixPublicFsSalts => 16975
  | .prefixZeroReserve => 17135
  | .atomicTerminalContext => 17535
  | .privateC1RootDuplicate => 17975
  | .privateC2RootDuplicate => 18007
  | .privateLaterRoots => 18039
  | .finalCoefficientsDuplicate => 18135
  | .relationChallengePoints => 18199
  | .relationOodValues => 18359
  | .relationOodMixes => 18487
  | .relationSumcheckRows => 18615
  | .relationFinalCoefficients => 19063
  | .finalGrindingNonce => 19127
  | .querySelector => 19135

def FixedSemanticSegment.bytes : FixedSemanticSegment → Nat
  | .accountMagic => 8
  | .gamma => 16
  | .candidateC1Duplicate => 5184
  | .c2Duplicate => 4032
  | .relationScales => 48
  | .relationPoints => 480
  | .relationClaimsDuplicate => 1216
  | .relationAlphas => 64
  | .relationFoldNoncesAndZeroPad => 64
  | .prefixHeader => 23
  | .prefixC1Root | .prefixC2Root => 32
  | .prefixInitialBClaim => 16
  | .prefixBSumcheck => 4480
  | .prefixPointClaims => 1216
  | .prefixTerminalReal | .prefixTerminalMask | .prefixTerminalMasked => 16
  | .prefixInactiveClaim => 16
  | .prefixPublicFsSalts => 160
  | .prefixZeroReserve => 400
  | .atomicTerminalContext => 440
  | .privateC1RootDuplicate | .privateC2RootDuplicate => 32
  | .privateLaterRoots => 96
  | .finalCoefficientsDuplicate => 64
  | .relationChallengePoints => 160
  | .relationOodValues => 128
  | .relationOodMixes => 128
  | .relationSumcheckRows => 448
  | .relationFinalCoefficients => 64
  | .finalGrindingNonce => 8
  | .querySelector => 1

def FixedSemanticSegment.stop (segment : FixedSemanticSegment) : Nat :=
  segment.start + segment.bytes

abbrev FixedSemanticByte :=
  (segment : FixedSemanticSegment) × Fin segment.bytes

def fixedSemanticByteOffset (coordinate : FixedSemanticByte) : Nat :=
  coordinate.1.start + coordinate.2.val

theorem fixed_semantic_offsets_match_repaired_parser :
    FixedSemanticSegment.start .accountMagic = magicOffset ∧
    FixedSemanticSegment.start .gamma = gammaOffset ∧
    FixedSemanticSegment.start .candidateC1Duplicate = candidateC1Offset ∧
    FixedSemanticSegment.start .c2Duplicate = c2Offset ∧
    FixedSemanticSegment.start .relationScales = relationScalesOffset ∧
    FixedSemanticSegment.start .relationPoints = relationPointsOffset ∧
    FixedSemanticSegment.start .relationClaimsDuplicate = relationClaimsOffset ∧
    FixedSemanticSegment.start .relationAlphas = relationAlphasOffset ∧
    FixedSemanticSegment.start .relationFoldNoncesAndZeroPad = relationFinalOffset ∧
    FixedSemanticSegment.start .prefixHeader = wirePrefixOffset ∧
    FixedSemanticSegment.start .atomicTerminalContext = atomicContextOffset ∧
    FixedSemanticSegment.start .privateC1RootDuplicate = privateRootsOffset ∧
    FixedSemanticSegment.start .finalCoefficientsDuplicate = finalCoefficientsOffset ∧
    FixedSemanticSegment.start .relationChallengePoints = relationStressOffset ∧
    FixedSemanticSegment.start .finalGrindingNonce = finalNonceOffset ∧
    FixedSemanticSegment.start .querySelector = querySelectorOffset ∧
    FixedSemanticSegment.stop .querySelector = repairedFixedBytes := by
  norm_num [FixedSemanticSegment.start, FixedSemanticSegment.stop,
    FixedSemanticSegment.bytes, magicOffset, gammaOffset, candidateC1Offset,
    c2Offset, relationScalesOffset, relationPointsOffset, relationClaimsOffset,
    relationAlphasOffset, relationFinalOffset, wirePrefixOffset,
    atomicContextOffset, privateRootsOffset, finalCoefficientsOffset,
    relationStressOffset, finalNonceOffset, querySelectorOffset,
    repairedFixedBytes]

theorem fixed_semantic_segment_within_repaired_prefix
    (segment : FixedSemanticSegment) :
    segment.stop ≤ repairedFixedBytes := by
  cases segment <;> norm_num [FixedSemanticSegment.stop,
    FixedSemanticSegment.start, FixedSemanticSegment.bytes, repairedFixedBytes]

theorem fixed_semantic_segments_pairwise_disjoint :
    ∀ first second : FixedSemanticSegment, first ≠ second →
      first.stop ≤ second.start ∨ second.stop ≤ first.start := by
  intro first second hne
  fin_cases first <;> fin_cases second <;>
    simp_all [FixedSemanticSegment.stop, FixedSemanticSegment.start,
      FixedSemanticSegment.bytes]

theorem fixed_semantic_byte_offset_lt (coordinate : FixedSemanticByte) :
    fixedSemanticByteOffset coordinate < repairedFixedBytes := by
  have hstop := fixed_semantic_segment_within_repaired_prefix coordinate.1
  have hlocal := coordinate.2.isLt
  simp only [fixedSemanticByteOffset, FixedSemanticSegment.stop] at hstop ⊢
  omega

def fixedSemanticByteFin (coordinate : FixedSemanticByte) : Fin repairedFixedBytes :=
  ⟨fixedSemanticByteOffset coordinate, fixed_semantic_byte_offset_lt coordinate⟩

theorem fixedSemanticByteFin_injective : Function.Injective fixedSemanticByteFin := by
  rintro ⟨leftSegment, leftByte⟩ ⟨rightSegment, rightByte⟩ equal
  simp only [fixedSemanticByteFin, Fin.mk.injEq, fixedSemanticByteOffset] at equal
  by_cases hsegment : leftSegment = rightSegment
  · subst rightSegment
    have hbyte : leftByte = rightByte := Fin.ext (by omega)
    subst rightByte
    rfl
  · have hdisjoint := fixed_semantic_segments_pairwise_disjoint
      leftSegment rightSegment hsegment
    have hleft := leftByte.isLt
    have hright := rightByte.isLt
    simp only [FixedSemanticSegment.stop] at hdisjoint
    omega

theorem fixed_semantic_layout_has_no_gaps :
    FixedSemanticSegment.start .accountMagic = 0 ∧
    FixedSemanticSegment.stop .accountMagic = FixedSemanticSegment.start .gamma ∧
    FixedSemanticSegment.stop .gamma = FixedSemanticSegment.start .candidateC1Duplicate ∧
    FixedSemanticSegment.stop .candidateC1Duplicate = FixedSemanticSegment.start .c2Duplicate ∧
    FixedSemanticSegment.stop .c2Duplicate = FixedSemanticSegment.start .relationScales ∧
    FixedSemanticSegment.stop .relationScales = FixedSemanticSegment.start .relationPoints ∧
    FixedSemanticSegment.stop .relationPoints =
      FixedSemanticSegment.start .relationClaimsDuplicate ∧
    FixedSemanticSegment.stop .relationClaimsDuplicate =
      FixedSemanticSegment.start .relationAlphas ∧
    FixedSemanticSegment.stop .relationAlphas =
      FixedSemanticSegment.start .relationFoldNoncesAndZeroPad ∧
    FixedSemanticSegment.stop .relationFoldNoncesAndZeroPad =
      FixedSemanticSegment.start .prefixHeader ∧
    FixedSemanticSegment.stop .prefixHeader = FixedSemanticSegment.start .prefixC1Root ∧
    FixedSemanticSegment.stop .prefixC1Root = FixedSemanticSegment.start .prefixC2Root ∧
    FixedSemanticSegment.stop .prefixC2Root = FixedSemanticSegment.start .prefixInitialBClaim ∧
    FixedSemanticSegment.stop .prefixInitialBClaim = FixedSemanticSegment.start .prefixBSumcheck ∧
    FixedSemanticSegment.stop .prefixBSumcheck = FixedSemanticSegment.start .prefixPointClaims ∧
    FixedSemanticSegment.stop .prefixPointClaims = FixedSemanticSegment.start .prefixTerminalReal ∧
    FixedSemanticSegment.stop .prefixTerminalReal = FixedSemanticSegment.start .prefixTerminalMask ∧
    FixedSemanticSegment.stop .prefixTerminalMask =
      FixedSemanticSegment.start .prefixTerminalMasked ∧
    FixedSemanticSegment.stop .prefixTerminalMasked =
      FixedSemanticSegment.start .prefixInactiveClaim ∧
    FixedSemanticSegment.stop .prefixInactiveClaim =
      FixedSemanticSegment.start .prefixPublicFsSalts ∧
    FixedSemanticSegment.stop .prefixPublicFsSalts =
      FixedSemanticSegment.start .prefixZeroReserve ∧
    FixedSemanticSegment.stop .prefixZeroReserve =
      FixedSemanticSegment.start .atomicTerminalContext ∧
    FixedSemanticSegment.stop .atomicTerminalContext =
      FixedSemanticSegment.start .privateC1RootDuplicate ∧
    FixedSemanticSegment.stop .privateC1RootDuplicate =
      FixedSemanticSegment.start .privateC2RootDuplicate ∧
    FixedSemanticSegment.stop .privateC2RootDuplicate =
      FixedSemanticSegment.start .privateLaterRoots ∧
    FixedSemanticSegment.stop .privateLaterRoots =
      FixedSemanticSegment.start .finalCoefficientsDuplicate ∧
    FixedSemanticSegment.stop .finalCoefficientsDuplicate =
      FixedSemanticSegment.start .relationChallengePoints ∧
    FixedSemanticSegment.stop .relationChallengePoints =
      FixedSemanticSegment.start .relationOodValues ∧
    FixedSemanticSegment.stop .relationOodValues = FixedSemanticSegment.start .relationOodMixes ∧
    FixedSemanticSegment.stop .relationOodMixes = FixedSemanticSegment.start .relationSumcheckRows ∧
    FixedSemanticSegment.stop .relationSumcheckRows =
      FixedSemanticSegment.start .relationFinalCoefficients ∧
    FixedSemanticSegment.stop .relationFinalCoefficients =
      FixedSemanticSegment.start .finalGrindingNonce ∧
    FixedSemanticSegment.stop .finalGrindingNonce = FixedSemanticSegment.start .querySelector ∧
    FixedSemanticSegment.stop .querySelector = repairedFixedBytes := by
  norm_num [FixedSemanticSegment.start, FixedSemanticSegment.stop,
    FixedSemanticSegment.bytes, repairedFixedBytes]

/-! The complete runtime body is indexed directly by its exact byte length.
The fine fixed-segment type above and the five imported suffix sections provide
the structured inventory; this `Fin` index prevents a hidden gap or duplicate
coordinate from being introduced by a separate encoding. -/

abbrev RuntimeBodyByte (shape : RuntimeShape) :=
  Fin (runtimeRepairedProofBytes shape)

theorem runtime_body_byte_count (shape : RuntimeShape) :
    Fintype.card (RuntimeBodyByte shape) = runtimeRepairedProofBytes shape :=
  Fintype.card_fin _

/-! ## Exact semantic classes -/

inductive CoverageClass where
  | publicWitnessIndependent
  | hiddenByA
  | hiddenByCorrelatedB
  | hiddenByDirectC
  | determinedByAuthenticatedIdentity
  | computationalCommitmentMetadata
  | honestSelectorMetadata
  deriving DecidableEq, Fintype

def pointClaimClass (lane : Nat) : CoverageClass :=
  if lane ≤ 16 then .hiddenByA
  else if lane = 17 then .hiddenByCorrelatedB
  else .hiddenByDirectC

def fixedSemanticByteClass (coordinate : FixedSemanticByte) : CoverageClass :=
  match coordinate.1 with
  | .accountMagic | .prefixHeader | .prefixPublicFsSalts | .prefixZeroReserve =>
      .publicWitnessIndependent
  | .candidateC1Duplicate | .c2Duplicate | .gamma | .relationScales |
      .relationPoints | .relationClaimsDuplicate | .relationAlphas |
      .relationFoldNoncesAndZeroPad | .prefixTerminalReal |
      .prefixTerminalMask | .prefixTerminalMasked | .atomicTerminalContext |
      .privateC1RootDuplicate | .privateC2RootDuplicate |
      .finalCoefficientsDuplicate | .relationChallengePoints |
      .relationOodMixes | .finalGrindingNonce =>
      .determinedByAuthenticatedIdentity
  | .prefixC1Root | .prefixC2Root | .privateLaterRoots =>
      .computationalCommitmentMetadata
  | .prefixInitialBClaim | .prefixBSumcheck | .prefixInactiveClaim =>
      .hiddenByCorrelatedB
  | .prefixPointClaims =>
      pointClaimClass ((coordinate.2.val / 16) % 19)
  | .relationOodValues | .relationSumcheckRows | .relationFinalCoefficients =>
      .hiddenByDirectC
  | .querySelector => .honestSelectorMetadata

def runtimeSuffixLocalClass (shape : RuntimeShape) (part : SuffixSection)
    (offset : Nat) : CoverageClass :=
  let count := shape.recordCount part
  let valueBytes := part.valueBytes
  let recordBytes := valueBytes + leafSaltBytes
  let recordsBytes := count * recordBytes
  if offset < 2 then
    .determinedByAuthenticatedIdentity
  else if offset < 2 + recordsBytes then
    let inRecord := (offset - 2) % recordBytes
    if inRecord < valueBytes then
      match part with
      | .c1 => .hiddenByA
      | .c2 =>
          if inRecord < 64 then .hiddenByA
          else if inRecord < 128 then .hiddenByCorrelatedB
          else .hiddenByDirectC
      | .later1 | .later2 | .later3 => .hiddenByDirectC
    else
      .publicWitnessIndependent
  else if offset < 2 + recordsBytes + 4 then
    .determinedByAuthenticatedIdentity
  else
    .computationalCommitmentMetadata

def repairedFixedOffsetClass (offset : Nat) : CoverageClass :=
  match fixedSpanAt offset with
  | .magic => .publicWitnessIndependent
  | .gamma | .candidateC1 | .c2 | .relationScales | .relationPoints |
      .relationClaims | .relationAlphas | .relationFinal =>
      .determinedByAuthenticatedIdentity
  | .wirePrefix =>
      let relative := offset - wirePrefixOffset
      if relative < 23 then .publicWitnessIndependent
      else if relative < 55 then .computationalCommitmentMetadata
      else if relative < 87 then .computationalCommitmentMetadata
      else if relative < 103 then .hiddenByCorrelatedB
      else if relative < 4583 then .hiddenByCorrelatedB
      else if relative < 5799 then
        pointClaimClass (((relative - 4583) / 16) % 19)
      else if relative < 5847 then .determinedByAuthenticatedIdentity
      else if relative < 5863 then .hiddenByCorrelatedB
      else .publicWitnessIndependent
  | .atomicContext => .determinedByAuthenticatedIdentity
  | .privateRoots =>
      if offset - privateRootsOffset < 64 then
        .determinedByAuthenticatedIdentity
      else
        .computationalCommitmentMetadata
  | .finalCoefficients => .determinedByAuthenticatedIdentity
  | .relationStress =>
      let relative := offset - relationStressOffset
      if relative < 160 then .determinedByAuthenticatedIdentity
      else if relative < 288 then .hiddenByDirectC
      else if relative < 416 then .determinedByAuthenticatedIdentity
      else .hiddenByDirectC
  | .finalNonce => .determinedByAuthenticatedIdentity
  | .querySelector => .honestSelectorMetadata

def runtimeBodyByteClass {shape : RuntimeShape}
    (coordinate : RuntimeBodyByte shape) : CoverageClass :=
  if coordinate.val < repairedFixedBytes then
    repairedFixedOffsetClass coordinate.val
  else
    let offset := coordinate.val - repairedFixedBytes
    let part := runtimeSuffixSectionAt shape offset
    runtimeSuffixLocalClass shape part (offset - runtimeSectionStart shape part)

def embedRepairedFixedByte (shape : RuntimeShape)
    (offset : Fin repairedFixedBytes) : RuntimeBodyByte shape :=
  ⟨offset.val, by
    have hoffset := offset.isLt
    simp only [runtimeRepairedProofBytes]
    omega⟩

theorem embedded_repaired_fixed_class_agrees
    (shape : RuntimeShape) (offset : Fin repairedFixedBytes) :
    runtimeBodyByteClass (embedRepairedFixedByte shape offset) =
      repairedFixedOffsetClass offset.val := by
  simp [runtimeBodyByteClass, embedRepairedFixedByte, offset.isLt]

theorem runtime_section_stop_le_suffix (shape : RuntimeShape)
    (part : SuffixSection) :
    runtimeSectionStop shape part ≤ runtimeSuffixBytes shape := by
  fin_cases part <;>
    simp [runtimeSectionStop, runtimeSectionStart, runtimeSuffixBytes] <;>
    omega

def embedRuntimeSuffixByte (shape : RuntimeShape) (part : SuffixSection)
    (byte : Fin (runtimeSectionBytes shape part)) : RuntimeBodyByte shape :=
  ⟨repairedFixedBytes + runtimeSectionStart shape part + byte.val, by
    have hstop := runtime_section_stop_le_suffix shape part
    have hbyte := byte.isLt
    simp only [runtimeRepairedProofBytes, runtimeSectionStop] at hstop ⊢
    omega⟩

theorem embedded_runtime_suffix_class_agrees
    (shape : RuntimeShape) (part : SuffixSection)
    (byte : Fin (runtimeSectionBytes shape part)) :
    runtimeBodyByteClass (embedRuntimeSuffixByte shape part byte) =
      runtimeSuffixLocalClass shape part byte.val := by
  have hbyte := byte.isLt
  have hstop := runtime_section_stop_le_suffix shape part
  have hoffset : runtimeSectionStart shape part + byte.val <
      runtimeSuffixBytes shape := by
    simp only [runtimeSectionStop] at hstop
    omega
  have hcontains : runtimeSectionStart shape part ≤
        runtimeSectionStart shape part + byte.val ∧
      runtimeSectionStart shape part + byte.val < runtimeSectionStop shape part := by
    simp only [runtimeSectionStop]
    omega
  have hpart := runtime_suffix_section_unique shape
    (runtimeSectionStart shape part + byte.val) hoffset part hcontains
  unfold runtimeBodyByteClass
  have hnot : ¬ (embedRuntimeSuffixByte shape part byte).val <
      repairedFixedBytes := by
    change ¬ repairedFixedBytes + runtimeSectionStart shape part + byte.val <
      repairedFixedBytes
    omega
  rw [if_neg hnot]
  have hsub : (embedRuntimeSuffixByte shape part byte).val - repairedFixedBytes =
      runtimeSectionStart shape part + byte.val := by
    change repairedFixedBytes + runtimeSectionStart shape part + byte.val -
      repairedFixedBytes = runtimeSectionStart shape part + byte.val
    omega
  simp only [hsub]
  rw [← hpart]
  have hlocal : runtimeSectionStart shape part + byte.val -
      runtimeSectionStart shape part = byte.val := by omega
  rw [hlocal]

def ClassifiedAs {shape : RuntimeShape}
    (coordinate : RuntimeBodyByte shape) (classification : CoverageClass) : Prop :=
  runtimeBodyByteClass coordinate = classification

theorem every_runtime_body_coordinate_has_exactly_one_class
    {shape : RuntimeShape} (coordinate : RuntimeBodyByte shape) :
    ∃! classification, ClassifiedAs coordinate classification := by
  exact ⟨runtimeBodyByteClass coordinate, rfl,
    fun classification hclassification => hclassification.symm⟩

theorem no_runtime_body_coordinate_has_two_distinct_classes
    {shape : RuntimeShape} (coordinate : RuntimeBodyByte shape)
    {left right : CoverageClass}
    (hleft : ClassifiedAs coordinate left)
    (hright : ClassifiedAs coordinate right) : left = right := by
  exact hleft.symm.trans hright

theorem every_runtime_byte_has_one_class
    (shape : RuntimeShape) (offset : RuntimeBodyByte shape) :
    ∃! classification : CoverageClass, ClassifiedAs offset classification :=
  every_runtime_body_coordinate_has_exactly_one_class offset

theorem current_fixture_runtime_body_has_exactly_75358_classified_bytes :
    Fintype.card (RuntimeBodyByte currentFixtureRuntimeShape) = 75358 := by
  rw [runtime_body_byte_count]
  exact current_fixture_repaired_proof_is_75358

theorem c2_first_record_A_B_C_and_salt_classes
    (shape : RuntimeShape) (hcount : 0 < shape.recordCount .c2) :
    runtimeSuffixLocalClass shape .c2 2 = .hiddenByA ∧
      runtimeSuffixLocalClass shape .c2 66 = .hiddenByCorrelatedB ∧
      runtimeSuffixLocalClass shape .c2 130 = .hiddenByDirectC ∧
      runtimeSuffixLocalClass shape .c2 194 = .publicWitnessIndependent := by
  simp [runtimeSuffixLocalClass, SuffixSection.valueBytes, c2ValueBytes,
    leafSaltBytes]
  omega

def runtimeFrontierLocalOffset (shape : RuntimeShape)
    (part : SuffixSection) : Nat :=
  2 + shape.recordCount part * (part.valueBytes + leafSaltBytes) + 4

theorem section_count_and_frontier_classes_are_exact
    (shape : RuntimeShape) (part : SuffixSection) :
    runtimeSuffixLocalClass shape part 0 = .determinedByAuthenticatedIdentity ∧
      runtimeSuffixLocalClass shape part (runtimeFrontierLocalOffset shape part) =
        .computationalCommitmentMetadata := by
  constructor
  · simp [runtimeSuffixLocalClass]
  · simp [runtimeSuffixLocalClass, runtimeFrontierLocalOffset]

theorem fixed_commitment_root_and_duplicate_classes_are_exact :
    repairedFixedOffsetClass 11135 = .computationalCommitmentMetadata ∧
      repairedFixedOffsetClass 11167 = .computationalCommitmentMetadata ∧
      repairedFixedOffsetClass 17975 = .determinedByAuthenticatedIdentity ∧
      repairedFixedOffsetClass 18007 = .determinedByAuthenticatedIdentity ∧
      repairedFixedOffsetClass 18039 = .computationalCommitmentMetadata := by
  norm_num [repairedFixedOffsetClass, fixedSpanAt, wirePrefixOffset,
    privateRootsOffset, magicOffset, gammaOffset, candidateC1Offset, c2Offset,
    relationScalesOffset, relationPointsOffset, relationClaimsOffset,
    relationAlphasOffset, relationFinalOffset, atomicContextOffset,
    finalCoefficientsOffset]

/-! ## Named coverage and executable-correspondence interfaces -/

structure ReleasedViewCoverageInterfaces where
  publicWitnessIndependent : Prop
  componentAViewCovered : Prop
  correlatedComponentBViewCovered : Prop
  directComponentCViewCovered : Prop
  authenticatedIdentitiesSound : Prop
  computationalPcsMerkleViewCovered : Prop
  honestLeastGoodSelectorWitnessIndependent : Prop

def CoverageClass.Discharged
    (interfaces : ReleasedViewCoverageInterfaces) : CoverageClass → Prop
  | .publicWitnessIndependent => interfaces.publicWitnessIndependent
  | .hiddenByA => interfaces.componentAViewCovered
  | .hiddenByCorrelatedB => interfaces.correlatedComponentBViewCovered
  | .hiddenByDirectC => interfaces.directComponentCViewCovered
  | .determinedByAuthenticatedIdentity => interfaces.authenticatedIdentitiesSound
  | .computationalCommitmentMetadata => interfaces.computationalPcsMerkleViewCovered
  | .honestSelectorMetadata => interfaces.honestLeastGoodSelectorWitnessIndependent

theorem complete_runtime_classification_is_covered_under_named_interfaces
    (interfaces : ReleasedViewCoverageInterfaces)
    (hpublic : interfaces.publicWitnessIndependent)
    (hA : interfaces.componentAViewCovered)
    (hB : interfaces.correlatedComponentBViewCovered)
    (hC : interfaces.directComponentCViewCovered)
    (hidentity : interfaces.authenticatedIdentitiesSound)
    (hcrypto : interfaces.computationalPcsMerkleViewCovered)
    (hselector : interfaces.honestLeastGoodSelectorWitnessIndependent)
    {shape : RuntimeShape} (coordinate : RuntimeBodyByte shape) :
    (runtimeBodyByteClass coordinate).Discharged interfaces := by
  cases runtimeBodyByteClass coordinate <;>
    assumption

def ExactRustRepairedSemanticCorrespondence
    (shape : RuntimeShape)
    (rustClass : Fin (runtimeRepairedProofBytes shape) → CoverageClass) : Prop :=
  ∀ coordinate : RuntimeBodyByte shape,
    rustClass coordinate = runtimeBodyByteClass coordinate

theorem rust_classification_of_exact_correspondence
    {shape : RuntimeShape}
    {rustClass : Fin (runtimeRepairedProofBytes shape) → CoverageClass}
    (hcorrespondence : ExactRustRepairedSemanticCorrespondence shape rustClass)
    (offset : Fin (runtimeRepairedProofBytes shape)) :
    rustClass offset = runtimeBodyByteClass offset :=
  hcorrespondence offset

/-! ## Selector, terminal, lane-order, and retired-layout teeth -/

def querySelectorCoordinate : FixedSemanticByte :=
  ⟨.querySelector, ⟨0, by norm_num [FixedSemanticSegment.bytes]⟩⟩

def querySelectorRuntimeByte (shape : RuntimeShape) : RuntimeBodyByte shape :=
  ⟨querySelectorOffset, by
    simp only [runtimeRepairedProofBytes]
    norm_num [querySelectorOffset, repairedFixedBytes]
    omega⟩

theorem query_selector_is_byte_19135_and_honest_metadata :
    fixedSemanticByteOffset querySelectorCoordinate = 19135 ∧
      fixedSemanticByteClass querySelectorCoordinate = .honestSelectorMetadata ∧
      ∀ shape, runtimeBodyByteClass (querySelectorRuntimeByte shape) =
        .honestSelectorMetadata := by
  refine ⟨rfl, rfl, ?_⟩
  intro shape
  simp [runtimeBodyByteClass, querySelectorRuntimeByte,
    repairedFixedOffsetClass, fixedSpanAt, querySelectorOffset,
    repairedFixedBytes, gammaOffset, candidateC1Offset, c2Offset,
    relationScalesOffset, relationPointsOffset, relationClaimsOffset,
    relationAlphasOffset, relationFinalOffset, wirePrefixOffset,
    atomicContextOffset, privateRootsOffset, finalCoefficientsOffset,
    relationStressOffset, finalNonceOffset]

theorem selected_good_acceptance_alone_does_not_discharge_selector_hiding :
    ∃ (Good : Unit → Bool) (schedules : Fin 3 → Unit)
        (choose : Bool → Fin 3),
      (∀ witness,
        AspisV5SelectedGoodVerifierRelation.verifierAccepts
          Good schedules (choose witness)) ∧
        ¬ AspisV5SelectedGoodVerifierRelation.SelectorMetadataWitnessIndependent choose :=
  AspisV5SelectedGoodVerifierRelation.selectedGood_acceptance_does_not_imply_selector_hiding

def prefixPointClaimOffset (point lane byte : Nat) : Nat :=
  15695 + 16 * (19 * point + lane) + byte

def prefixPointClaimLaneMajorOffset (point lane byte : Nat) : Nat :=
  15695 + 16 * (4 * lane + point) + byte

theorem point_major_is_not_lane_major :
    prefixPointClaimOffset 1 0 0 = 15999 ∧
      prefixPointClaimLaneMajorOffset 1 0 0 = 15711 ∧
      prefixPointClaimOffset 1 0 0 ≠ prefixPointClaimLaneMajorOffset 1 0 0 := by
  norm_num [prefixPointClaimOffset, prefixPointClaimLaneMajorOffset]

theorem swapping_b_and_c_claim_lanes_changes_repaired_wire :
    prefixPointClaimOffset 0 17 0 = 15967 ∧
      prefixPointClaimOffset 0 18 0 = 15983 ∧
      prefixPointClaimOffset 0 17 0 ≠ prefixPointClaimOffset 0 18 0 := by
  norm_num [prefixPointClaimOffset]

def candidateC1SlotMajorOffset (slot lane byte : Nat) : Nat :=
  24 + (16 * slot + lane) * 4 + byte

def candidateC1LaneMajorOffset (slot lane byte : Nat) : Nat :=
  24 + (4 * lane + slot) * 4 + byte

theorem candidate_c1_slot_transposition_changes_repaired_wire :
    candidateC1SlotMajorOffset 1 0 0 = 88 ∧
      candidateC1LaneMajorOffset 1 0 0 = 28 ∧
      candidateC1SlotMajorOffset 1 0 0 ≠ candidateC1LaneMajorOffset 1 0 0 := by
  norm_num [candidateC1SlotMajorOffset, candidateC1LaneMajorOffset]

def firstFixedC1DuplicateByte : FixedSemanticByte :=
  ⟨.candidateC1Duplicate, ⟨0, by norm_num [FixedSemanticSegment.bytes]⟩⟩

def firstFixedC1RuntimeByte (shape : RuntimeShape) : RuntimeBodyByte shape :=
  ⟨candidateC1Offset, by
    simp only [runtimeRepairedProofBytes]
    norm_num [candidateC1Offset, repairedFixedBytes]
    omega⟩

def firstSuffixC1ValueLocalByte (shape : RuntimeShape)
    (hcount : 0 < shape.recordCount .c1) :
    Fin (runtimeSectionBytes shape .c1) :=
  ⟨2, by
    simp [runtimeSectionBytes, SuffixSection.valueBytes,
      candidateC1ValueBytes, leafSaltBytes]
    omega⟩

theorem fixed_c1_is_determined_and_suffix_c1_is_the_primitive_A_release
    (shape : RuntimeShape) (hcount : 0 < shape.recordCount .c1) :
    fixedSemanticByteClass firstFixedC1DuplicateByte =
        .determinedByAuthenticatedIdentity ∧
      runtimeBodyByteClass (firstFixedC1RuntimeByte shape) =
        .determinedByAuthenticatedIdentity ∧
      runtimeBodyByteClass
        (embedRuntimeSuffixByte shape .c1
          (firstSuffixC1ValueLocalByte shape hcount)) = .hiddenByA := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [runtimeBodyByteClass, firstFixedC1RuntimeByte,
      repairedFixedOffsetClass, fixedSpanAt, candidateC1Offset,
      repairedFixedBytes, gammaOffset, c2Offset]
  · rw [embedded_runtime_suffix_class_agrees]
    simp [runtimeSuffixLocalClass, firstSuffixC1ValueLocalByte,
      SuffixSection.valueBytes,
      candidateC1ValueBytes, leafSaltBytes]
    omega

def firstPrefixTerminalRealByte : FixedSemanticByte :=
  ⟨.prefixTerminalReal, ⟨0, by norm_num [FixedSemanticSegment.bytes]⟩⟩

def firstPrefixTerminalMaskByte : FixedSemanticByte :=
  ⟨.prefixTerminalMask, ⟨0, by norm_num [FixedSemanticSegment.bytes]⟩⟩

def firstPrefixTerminalMaskedByte : FixedSemanticByte :=
  ⟨.prefixTerminalMasked, ⟨0, by norm_num [FixedSemanticSegment.bytes]⟩⟩

def prefixTerminalRealOffset : Fin repairedFixedBytes :=
  ⟨16911, by norm_num [repairedFixedBytes]⟩

def prefixTerminalMaskOffset : Fin repairedFixedBytes :=
  ⟨16927, by norm_num [repairedFixedBytes]⟩

def prefixTerminalMaskedOffset : Fin repairedFixedBytes :=
  ⟨16943, by norm_num [repairedFixedBytes]⟩

theorem b_terminal_identity_coordinates_are_not_independently_masked_twice :
    fixedSemanticByteClass firstPrefixTerminalRealByte =
        .determinedByAuthenticatedIdentity ∧
      fixedSemanticByteClass firstPrefixTerminalMaskByte =
        .determinedByAuthenticatedIdentity ∧
      fixedSemanticByteClass firstPrefixTerminalMaskedByte =
        .determinedByAuthenticatedIdentity ∧
      ∀ shape,
        runtimeBodyByteClass
            (embedRepairedFixedByte shape prefixTerminalRealOffset) =
              .determinedByAuthenticatedIdentity ∧
          runtimeBodyByteClass
            (embedRepairedFixedByte shape prefixTerminalMaskOffset) =
              .determinedByAuthenticatedIdentity ∧
          runtimeBodyByteClass
            (embedRepairedFixedByte shape prefixTerminalMaskedOffset) =
              .determinedByAuthenticatedIdentity := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro shape
  simp [embedded_repaired_fixed_class_agrees, repairedFixedOffsetClass,
    prefixTerminalRealOffset, prefixTerminalMaskOffset,
    prefixTerminalMaskedOffset, fixedSpanAt, wirePrefixOffset,
    gammaOffset, candidateC1Offset, c2Offset,
    relationScalesOffset, relationPointsOffset, relationClaimsOffset,
    relationAlphasOffset, relationFinalOffset, atomicContextOffset]

theorem retired_width26_span_has_no_repaired_coordinate_and_is_rejected
    (shape : RuntimeShape) :
    FixedSemanticSegment.stop .querySelector = 19136 ∧
      runtimeFormerProofBytes shape = runtimeRepairedProofBytes shape + 8064 ∧
      parseRuntimeExact shape
        (List.replicate (runtimeFormerProofBytes shape) (0 : Byte)) = none := by
  refine ⟨by norm_num [FixedSemanticSegment.stop, FixedSemanticSegment.start,
      FixedSemanticSegment.bytes], ?_,
    former_layout_is_rejected_by_runtime_exact_parser shape⟩
  simp only [runtimeFormerProofBytes, runtimeRepairedProofBytes, formerFixedBytes]
  rw [retired_production_c1_span_is_8064]
  omega

theorem repaired_runtime_rejects_truncation_and_append (shape : RuntimeShape) :
    parseRuntimeExact shape
        (List.replicate (runtimeRepairedProofBytes shape - 1) (0 : Byte)) = none ∧
      parseRuntimeExact shape
        (List.replicate (runtimeRepairedProofBytes shape + 1) (0 : Byte)) = none := by
  exact ⟨one_byte_truncation_is_rejected_for_every_runtime_shape shape,
    one_byte_append_is_rejected_for_every_runtime_shape shape⟩

def runtimeDirectCReleasedRows (shape : RuntimeShape) : Nat :=
  40 + 4 * (shape.recordCount .later1 + shape.recordCount .later2 +
    shape.recordCount .later3)

theorem direct_c_runtime_rows_match_deployed_downstream_map
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (schedule : DeployedRuntimeSchedule F K)
    (shape : RuntimeShape)
    (hshape : shape.recordCount .later1 = schedule.later1Count ∧
      shape.recordCount .later2 = schedule.later2Count ∧
      shape.recordCount .later3 = schedule.later3Count) :
    runtimeDirectCReleasedRows shape = fRows (decodeFriSchedule schedule) := by
  rw [deployed_output_dimension schedule]
  simp only [runtimeDirectCReleasedRows, hshape.1, hshape.2.1, hshape.2.2]

#print axioms fixed_semantic_offsets_match_repaired_parser
#print axioms fixed_semantic_segment_within_repaired_prefix
#print axioms fixed_semantic_segments_pairwise_disjoint
#print axioms fixed_semantic_byte_offset_lt
#print axioms fixedSemanticByteFin_injective
#print axioms fixed_semantic_layout_has_no_gaps
#print axioms runtime_body_byte_count
#print axioms embedded_repaired_fixed_class_agrees
#print axioms runtime_section_stop_le_suffix
#print axioms embedded_runtime_suffix_class_agrees
#print axioms every_runtime_body_coordinate_has_exactly_one_class
#print axioms no_runtime_body_coordinate_has_two_distinct_classes
#print axioms every_runtime_byte_has_one_class
#print axioms current_fixture_runtime_body_has_exactly_75358_classified_bytes
#print axioms c2_first_record_A_B_C_and_salt_classes
#print axioms section_count_and_frontier_classes_are_exact
#print axioms fixed_commitment_root_and_duplicate_classes_are_exact
#print axioms complete_runtime_classification_is_covered_under_named_interfaces
#print axioms rust_classification_of_exact_correspondence
#print axioms query_selector_is_byte_19135_and_honest_metadata
#print axioms selected_good_acceptance_alone_does_not_discharge_selector_hiding
#print axioms point_major_is_not_lane_major
#print axioms swapping_b_and_c_claim_lanes_changes_repaired_wire
#print axioms candidate_c1_slot_transposition_changes_repaired_wire
#print axioms fixed_c1_is_determined_and_suffix_c1_is_the_primitive_A_release
#print axioms b_terminal_identity_coordinates_are_not_independently_masked_twice
#print axioms retired_width26_span_has_no_repaired_coordinate_and_is_rejected
#print axioms repaired_runtime_rejects_truncation_and_append
#print axioms direct_c_runtime_rows_match_deployed_downstream_map

end AspisFormal.V5RepairedRuntimeWireClassification
