import Mathlib

/-!
# Exact fixed-field and transcript grammar for the V6 one-fold verifier

This file is the mathematical specification of
`crates/aspis-core/src/v6_transcript.rs`.  It records the corrected three-row,
twenty-nine-column claim table, every fixed-field offset, the two reconstructed
sumcheck coefficients, and the order of the deterministic accepted-path
operations.

It does not claim that Rust follows this specification.  The source-to-model
obligations are stated separately in `V6AcceptedPathObligations`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisV6TranscriptRelationGrammar

/-! ## Frozen profile constants -/

def c1Columns : Nat := 26
def c2Columns : Nat := 3
def totalColumns : Nat := 29
def semanticRounds : Nat := 10
def semanticSentValues : Nat := 27
def pointClaimRows : Nat := 3
def relationRounds : Nat := 4
def relationSentValues : Nat := 6
def finalCoefficientCount : Nat := 256
def queryCount : Nat := 16
def querySelectorCount : Nat := 3
def compactDrawCap : Nat := 8
def queryDrawLimit : Nat := 64
def treeDepth : Nat := 18
def frontierCapPerTree : Nat := 209

def batchWorkBits : Nat := 34
def foldWorkBits : Nat := 31
def finalWorkBits : Nat := 34

/-- Byte-for-byte contents of `V6_PROFILE_BINDING`, represented as naturals
so this module does not depend on a Rust byte type. -/
def profileBinding : List Nat :=
  [65, 86, 54, 79, 70, 48, 48, 49,
    26, 3, 10, 16, 209, 0, 3, 10,
    27, 4, 6, 34, 31, 34, 112, 240,
    129, 2, 0, 1, 20, 18, 1, 0]

theorem exact_profile_binding :
    profileBinding.length = 32 ∧
      profileBinding.take 8 = [65, 86, 54, 79, 70, 48, 48, 49] ∧
      profileBinding[8]? = some c1Columns ∧
      profileBinding[9]? = some c2Columns ∧
      profileBinding[12]? = some frontierCapPerTree ∧
      profileBinding[24]? = some 129 ∧
      profileBinding[25]? = some 2 := by
  decide

theorem exact_profile_dimensions :
    totalColumns = c1Columns + c2Columns ∧
      pointClaimRows * totalColumns = 87 ∧
      querySelectorCount * compactDrawCap = 24 ∧
      2 ^ treeDepth = 262144 := by
  norm_num [totalColumns, c1Columns, c2Columns, pointClaimRows,
    querySelectorCount, compactDrawCap, treeDepth]

/-! ## Exact fixed-field layout -/

def initialClaimOffset : Nat := 0
def semanticOffset : Nat := 1
def semanticFieldCount : Nat := semanticRounds * semanticSentValues
def pointClaimsOffset : Nat := semanticOffset + semanticFieldCount
def pointClaimFieldCount : Nat := pointClaimRows * totalColumns
def inactiveClaimOffset : Nat := pointClaimsOffset + pointClaimFieldCount
def oodOffset : Nat := inactiveClaimOffset + 1
def oodFieldCount : Nat := 2
def relationOffset : Nat := oodOffset + oodFieldCount
def relationFieldCount : Nat := relationRounds * relationSentValues
def finalOffset : Nat := relationOffset + relationFieldCount
def fixedFieldCount : Nat := finalOffset + finalCoefficientCount

def m31LimbBits : Nat := 31
def limbsPerQM31 : Nat := 4
def fixedPackedLimbCount : Nat := fixedFieldCount * limbsPerQM31
def fixedPackedUsedBits : Nat := fixedPackedLimbCount * m31LimbBits
def fixedPackedByteCount : Nat := (fixedPackedUsedBits + 7) / 8
def fixedPackedCapacityBits : Nat := fixedPackedByteCount * 8
def fixedPackedPaddingBits : Nat :=
  fixedPackedCapacityBits - fixedPackedUsedBits

theorem exact_fixed_field_offsets :
    initialClaimOffset = 0 ∧
      semanticOffset = 1 ∧
      semanticFieldCount = 270 ∧
      pointClaimsOffset = 271 ∧
      pointClaimFieldCount = 87 ∧
      inactiveClaimOffset = 358 ∧
      oodOffset = 359 ∧
      relationOffset = 361 ∧
      relationFieldCount = 24 ∧
      finalOffset = 385 ∧
      fixedFieldCount = 641 := by
  norm_num [initialClaimOffset, semanticOffset, semanticFieldCount,
    semanticRounds, semanticSentValues, pointClaimsOffset,
    pointClaimFieldCount, pointClaimRows, totalColumns, inactiveClaimOffset,
    oodOffset, oodFieldCount, relationOffset, relationFieldCount,
    relationRounds, relationSentValues, finalOffset, fixedFieldCount,
    finalCoefficientCount]

/-- The packed fixed section uses the low four bits of its final byte and no
others.  The Rust parser now checks the remaining high nibble before either
the strict or deferred field decoder can accept the body. -/
theorem exact_fixed_packed_dimensions :
    fixedPackedLimbCount = 2564 ∧
      fixedPackedUsedBits = 79484 ∧
      fixedPackedByteCount = 9936 ∧
      fixedPackedCapacityBits = 79488 ∧
      fixedPackedPaddingBits = 4 ∧
      fixedPackedUsedBits % 8 = 4 := by
  norm_num [fixedPackedLimbCount, fixedFieldCount, finalOffset,
    relationOffset, oodOffset, inactiveClaimOffset, pointClaimsOffset,
    semanticOffset, semanticFieldCount, semanticRounds, semanticSentValues,
    pointClaimFieldCount, pointClaimRows, totalColumns, oodFieldCount,
    relationFieldCount, relationRounds, relationSentValues,
    finalCoefficientCount, limbsPerQM31, m31LimbBits,
    fixedPackedUsedBits, fixedPackedByteCount, fixedPackedCapacityBits,
    fixedPackedPaddingBits]

/-- Exact high-nibble-zero condition checked by the source predicate
`last_byte & 0xf0 == 0`. -/
def CanonicalFixedPadding (lastByte : Fin 256) : Prop :=
  lastByte.val < 16

theorem canonical_fixed_padding_iff_high_nibble_zero
    (lastByte : Fin 256) :
    CanonicalFixedPadding lastByte ↔ lastByte.val < 16 := by
  rfl

/-! ## Complete one-fold body dimensions -/

def c1QueryLimbCount : Nat := queryCount * 4 * c1Columns
def c1QueryPackedBytes : Nat := c1QueryLimbCount * m31LimbBits / 8
def c2QueryLimbCount : Nat := queryCount * 4 * c2Columns * limbsPerQM31
def c2QueryPackedBytes : Nat := c2QueryLimbCount * m31LimbBits / 8
def perQueryC1PackedBytes : Nat := 4 * c1Columns * m31LimbBits / 8
def perQueryC2PackedBytes : Nat := 4 * c2Columns * limbsPerQM31 * m31LimbBits / 8
def perQueryRecordBytes : Nat :=
  perQueryC1PackedBytes + perQueryC2PackedBytes + 32
def querySectionBytes : Nat := queryCount * perQueryRecordBytes
def rootBytes : Nat := 2 * 32
def workNonceBytes : Nat := 3 * 8
def bodyWithoutFrontiersBytes : Nat :=
  fixedPackedByteCount + rootBytes + workNonceBytes + querySectionBytes
def maximumFrontierBytes : Nat := 2 * frontierCapPerTree * 32
def maximumBodyBytes : Nat := bodyWithoutFrontiersBytes + maximumFrontierBytes

theorem exact_complete_body_dimensions :
    c1QueryLimbCount = 1664 ∧
      c1QueryPackedBytes = 6448 ∧
      c2QueryLimbCount = 768 ∧
      c2QueryPackedBytes = 2976 ∧
      perQueryC1PackedBytes = 403 ∧
      perQueryC2PackedBytes = 186 ∧
      perQueryRecordBytes = 621 ∧
      querySectionBytes = 9936 ∧
      bodyWithoutFrontiersBytes = 19960 ∧
      maximumFrontierBytes = 13376 ∧
      maximumBodyBytes = 33336 ∧
      maximumBodyBytes < 40960 := by
  norm_num [c1QueryLimbCount, queryCount, c1Columns, c1QueryPackedBytes,
    m31LimbBits, c2QueryLimbCount, c2Columns, limbsPerQM31,
    c2QueryPackedBytes, perQueryC1PackedBytes, perQueryC2PackedBytes,
    perQueryRecordBytes, querySectionBytes, rootBytes, workNonceBytes,
    bodyWithoutFrontiersBytes, fixedPackedByteCount, fixedPackedUsedBits,
    fixedPackedLimbCount, fixedFieldCount, finalOffset, relationOffset,
    oodOffset, inactiveClaimOffset, pointClaimsOffset, semanticOffset,
    semanticFieldCount, semanticRounds, semanticSentValues,
    pointClaimFieldCount, pointClaimRows, totalColumns, oodFieldCount,
    relationFieldCount, relationRounds, relationSentValues,
    finalCoefficientCount, maximumFrontierBytes, frontierCapPerTree,
    maximumBodyBytes]

def semanticFieldIndex (round : Fin 10) (sent : Fin 27) : Fin 641 :=
  ⟨1 + round.val * 27 + sent.val, by omega⟩

def pointClaimFieldIndex (row : Fin 3) (column : Fin 29) : Fin 641 :=
  ⟨271 + row.val * 29 + column.val, by omega⟩

def oodFieldIndex (sample : Fin 2) : Fin 641 :=
  ⟨359 + sample.val, by omega⟩

def relationFieldIndex (round : Fin 4) (sent : Fin 6) : Fin 641 :=
  ⟨361 + round.val * 6 + sent.val, by omega⟩

def finalFieldIndex (coefficient : Fin 256) : Fin 641 :=
  ⟨385 + coefficient.val, by omega⟩

theorem point_claim_rows_are_contiguous
    (row : Fin 3) (column : Fin 29) :
    (pointClaimFieldIndex row column).val =
      271 + row.val * 29 + column.val := by
  rfl

theorem point_claim_field_index_injective :
    Function.Injective (fun slot : Fin 3 × Fin 29 =>
      pointClaimFieldIndex slot.1 slot.2) := by
  intro left right equal
  have value := congrArg Fin.val equal
  simp only [pointClaimFieldIndex] at value
  have rows : left.1.val = right.1.val := by omega
  have columns : left.2.val = right.2.val := by omega
  exact Prod.ext (Fin.ext rows) (Fin.ext columns)

/-- The temporal fixed-field permutation in
`verify_v6_transcript_and_relation`. Positions `0..366` are consumed in wire
order, then final-vector fields `385..640`, then the remaining relation fields
`367..384`. -/
def fixedFieldPermutation (position : Fin 641) : Fin 641 :=
  if first : position.val < 367 then
    ⟨position.val, by omega⟩
  else if finalBlock : position.val < 623 then
    ⟨385 + (position.val - 367), by omega⟩
  else
    ⟨367 + (position.val - 623), by omega⟩

def fixedFieldConsumptionOrder : List Nat :=
  List.ofFn fun position : Fin 641 => (fixedFieldPermutation position).val

theorem fixed_field_permutation_injective :
    Function.Injective fixedFieldPermutation := by
  intro left right equal
  apply Fin.ext
  have value := congrArg Fin.val equal
  by_cases leftFirst : left.val < 367 <;>
    by_cases rightFirst : right.val < 367 <;>
    by_cases leftFinal : left.val < 623 <;>
    by_cases rightFinal : right.val < 623 <;>
    simp [fixedFieldPermutation, leftFirst, rightFirst,
      leftFinal, rightFinal] at value <;> omega

theorem fixed_field_consumption_length :
    fixedFieldConsumptionOrder.length = 641 := by
  simp only [fixedFieldConsumptionOrder, List.length_ofFn]

theorem fixed_field_consumption_has_no_duplicates :
    fixedFieldConsumptionOrder.Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro left right equal
  have permutationEqual : fixedFieldPermutation left =
      fixedFieldPermutation right := Fin.ext equal
  exact fixed_field_permutation_injective permutationEqual

theorem fixed_field_consumption_covers_exactly_the_wire :
    fixedFieldConsumptionOrder.toFinset = Finset.range 641 := by
  ext value
  constructor
  · intro member
    rw [List.mem_toFinset] at member
    simp only [fixedFieldConsumptionOrder, List.mem_ofFn] at member
    obtain ⟨position, rfl⟩ := member
    exact Finset.mem_range.mpr (fixedFieldPermutation position).isLt
  · intro member
    have valueLt : value < 641 := Finset.mem_range.mp member
    have surjective : Function.Surjective fixedFieldPermutation :=
      (Finite.injective_iff_surjective).mp fixed_field_permutation_injective
    obtain ⟨position, positionValue⟩ := surjective ⟨value, valueLt⟩
    rw [List.mem_toFinset]
    simp only [fixedFieldConsumptionOrder, List.mem_ofFn]
    exact ⟨position, congrArg Fin.val positionValue⟩

theorem every_fixed_field_is_consumed_once (index : Fin 641) :
    index.val ∈ fixedFieldConsumptionOrder ∧
      fixedFieldConsumptionOrder.count index.val = 1 := by
  constructor
  · have : index.val ∈ Finset.range 641 := by simp
    rw [← fixed_field_consumption_covers_exactly_the_wire] at this
    simpa using this
  · apply List.count_eq_one_of_mem fixed_field_consumption_has_no_duplicates
    have : index.val ∈ Finset.range 641 := by simp
    rw [← fixed_field_consumption_covers_exactly_the_wire] at this
    simpa using this

/-! ## The corrected `3 × 29` point-claim table -/

abbrev PointClaimSlot := Fin 3 × Fin 29
abbrev TerminalClaimSlot := Fin 3 × Fin 28

def terminalUsesPointClaim (slot : PointClaimSlot) : Prop :=
  slot.2.val < 28

theorem exact_point_and_terminal_claim_counts :
    Fintype.card PointClaimSlot = 87 ∧
      Fintype.card TerminalClaimSlot = 84 := by
  norm_num

/-- Column 28 is the appended `D` lane.  The PCS relation consumes it, while
the maintained selected-hiding terminal consumes columns 0 through 27. -/
theorem terminal_excludes_exactly_d_lane (row : Fin 3) :
    ¬ terminalUsesPointClaim (row, (⟨28, by omega⟩ : Fin 29)) ∧
      ∀ column : Fin 29,
        ¬ terminalUsesPointClaim (row, column) → column.val = 28 := by
  constructor
  · simp [terminalUsesPointClaim]
  · intro column excluded
    simp only [terminalUsesPointClaim, not_lt] at excluded
    omega

theorem relation_uses_all_twenty_nine_lanes (_row : Fin 3) :
    (Finset.univ : Finset (Fin 29)).card = 29 ∧
      ∀ column : Fin 29, column ∈ (Finset.univ : Finset (Fin 29)) := by
  simp

/-! ## Fixed-field values and reconstructed coefficients -/

structure FixedFieldView (K : Type*) where
  initialClaim : K
  semanticSent : Fin 10 → Fin 27 → K
  pointClaim : Fin 3 → Fin 29 → K
  inactiveClaim : K
  oodValue : Fin 2 → K
  relationSent : Fin 4 → Fin 6 → K
  finalCoefficient : Fin 256 → K

structure SemanticRoundParts (K : Type*) where
  constant : K
  higher : Fin 26 → K

def SemanticRoundParts.sent {K : Type*}
    (parts : SemanticRoundParts K) (sent : Fin 27) : K :=
  if sent.val = 0 then parts.constant
  else parts.higher ⟨sent.val - 1, by omega⟩

def reconstructedSemanticLinear {K : Type*} [Field K]
    (runningClaim : K) (parts : SemanticRoundParts K) : K :=
  runningClaim -
    (parts.constant + parts.constant + ∑ index, parts.higher index)

def semanticBoundaryFromParts {K : Type*} [Field K]
    (linear : K) (parts : SemanticRoundParts K) : K :=
  parts.constant + parts.constant + linear + ∑ index, parts.higher index

theorem reconstructed_semantic_linear_has_exact_boundary
    {K : Type*} [Field K]
    (runningClaim : K) (parts : SemanticRoundParts K) :
    semanticBoundaryFromParts
        (reconstructedSemanticLinear runningClaim parts) parts =
      runningClaim := by
  simp only [semanticBoundaryFromParts, reconstructedSemanticLinear]
  ring

def semanticCoefficient {K : Type*} [Field K]
    (runningClaim : K) (parts : SemanticRoundParts K)
    (coefficient : Fin 28) : K :=
  if coefficient.val = 0 then parts.constant
  else if coefficient.val = 1 then
    reconstructedSemanticLinear runningClaim parts
  else parts.higher ⟨coefficient.val - 2, by omega⟩

def semanticEvaluate {K : Type*} [Field K]
    (runningClaim : K) (parts : SemanticRoundParts K) (challenge : K) : K :=
  ∑ coefficient : Fin 28,
    semanticCoefficient runningClaim parts coefficient *
      challenge ^ coefficient.val

structure RelationRoundParts (K : Type*) where
  c0 : K
  c1 : K
  c2 : K
  c3 : K
  c5 : K
  c6 : K

def RelationRoundParts.sent {K : Type*}
    (parts : RelationRoundParts K) (sent : Fin 6) : K :=
  ![parts.c0, parts.c1, parts.c2, parts.c3, parts.c5, parts.c6] sent

def reconstructedRelationQuartic {K : Type*} [Field K]
    (quarter runningClaim : K) (parts : RelationRoundParts K) : K :=
  runningClaim * quarter - parts.c0

def relationBoundaryFromParts {K : Type*} [Field K]
    (quartic : K) (parts : RelationRoundParts K) : K :=
  (parts.c0 + quartic) * 4

theorem reconstructed_relation_quartic_has_exact_boundary
    {K : Type*} [Field K]
    (quarter runningClaim : K) (parts : RelationRoundParts K)
    (quarterExact : quarter * 4 = (1 : K)) :
    relationBoundaryFromParts
        (reconstructedRelationQuartic quarter runningClaim parts) parts =
      runningClaim := by
  calc
    relationBoundaryFromParts
        (reconstructedRelationQuartic quarter runningClaim parts) parts =
        runningClaim * (quarter * 4) := by
          simp only [relationBoundaryFromParts,
            reconstructedRelationQuartic]
          ring
    _ = runningClaim := by rw [quarterExact, mul_one]

def relationCoefficient {K : Type*} [Field K]
    (quarter runningClaim : K) (parts : RelationRoundParts K)
    (coefficient : Fin 7) : K :=
  ![parts.c0, parts.c1, parts.c2, parts.c3,
    reconstructedRelationQuartic quarter runningClaim parts,
    parts.c5, parts.c6] coefficient

def relationEvaluate {K : Type*} [Field K]
    (quarter runningClaim : K) (parts : RelationRoundParts K)
    (challenge : K) : K :=
  ∑ coefficient : Fin 7,
    relationCoefficient quarter runningClaim parts coefficient *
      challenge ^ coefficient.val

def relationSentCoefficientOrder : List Nat := [0, 1, 2, 3, 5, 6]

theorem exact_relation_sent_coefficient_order :
    relationSentCoefficientOrder = [0, 1, 2, 3, 5, 6] ∧
      relationSentCoefficientOrder.Nodup ∧
      4 ∉ relationSentCoefficientOrder := by
  decide

/-! ## Exact accepted execution order -/

inductive WorkStage where
  | batch
  | fold
  | final
  deriving DecidableEq, Fintype

def workBits : WorkStage → Nat
  | .batch => batchWorkBits
  | .fold => foldWorkBits
  | .final => finalWorkBits

theorem exact_work_bits :
    workBits .batch = 34 ∧
      workBits .fold = 31 ∧
      workBits .final = 34 := by
  decide

inductive ExecutionOperation where
  | absorbProfile
  | absorbCircleBasis
  | absorbDeploymentContext
  | absorbStatement
  | absorbHidingPrecommit
  | absorbC1RootAndSalt
  | squeezeLambda
  | squeezeChi
  | absorbC2RootAndSalt
  | absorbConstraintRegistry
  | absorbHelperSum
  | squeezeTheta
  | squeezeZerocheckCoordinate (coordinate : Fin 10)
  | squeezeMu
  | absorbMaskedInitialClaim
  | squeezeEtaNonzero
  | absorbSemanticRound (round : Fin 10)
  | squeezeSemanticRound (round : Fin 10)
  | absorbPointClaims3x29
  | checkSemanticTerminal
  | checkWork (stage : WorkStage)
  | absorbWork (stage : WorkStage)
  | squeezeGammaNonzero
  | absorbInactiveClaim
  | squeezeKappaNonzero
  | squeezeCirclePoint (sample : Fin 2)
  | absorbOodValue (sample : Fin 2)
  | squeezeOodMix (sample : Fin 2)
  | absorbRelationRound (round : Fin 4)
  | squeezeRelationAlpha (round : Fin 4)
  | foldRelationWeights (round : Fin 4)
  | absorbFinal256
  | deriveFirstCompactQueries
  | checkFrontierCounts
  | adoptSelectedQueryTranscript
  | absorbQueryBatchChallengeDomain
  | squeezeQueryBatchRhoNonzero
  | authenticateAndFoldQueries
  | addQueryBatchWeightsAndClaim
  | absorbQueryBatchClaim
  | foldDisclosedFinal (round : Fin 3)
  | checkRelationTerminal
  deriving DecidableEq

structure AbsorbFrame where
  label : Nat
  payloadBytes : Nat
  deriving DecidableEq

/-- Exact label and payload width of every fixed accepted-path absorb.  A
`none` entry is a squeeze, a predicate check, or an in-memory fold. -/
def absorbFrame : ExecutionOperation → Option AbsorbFrame
  | .absorbProfile => some ⟨1, 32⟩
  | .absorbCircleBasis => some ⟨11, 22⟩
  | .absorbDeploymentContext => some ⟨47, 64⟩
  | .absorbStatement => some ⟨2, 32⟩
  | .absorbHidingPrecommit => some ⟨30, 81⟩
  | .absorbC1RootAndSalt => some ⟨12, 65⟩
  | .absorbC2RootAndSalt => some ⟨13, 64⟩
  | .absorbConstraintRegistry => some ⟨32, 28⟩
  | .absorbHelperSum => some ⟨33, 16⟩
  | .absorbMaskedInitialClaim => some ⟨31, 18⟩
  | .absorbSemanticRound _ => some ⟨48, 433⟩
  | .absorbPointClaims3x29 => some ⟨49, 1392⟩
  | .absorbWork .batch => some ⟨28, 8⟩
  | .absorbWork .fold => some ⟨20, 9⟩
  | .absorbWork .final => some ⟨5, 8⟩
  | .absorbInactiveClaim => some ⟨50, 16⟩
  | .absorbOodValue _ => some ⟨51, 17⟩
  | .absorbRelationRound _ => some ⟨52, 97⟩
  | .absorbFinal256 => some ⟨53, 4096⟩
  | .absorbQueryBatchChallengeDomain => some ⟨55, 0⟩
  | .absorbQueryBatchClaim => some ⟨56, 16⟩
  | _ => none

theorem exact_dynamic_absorb_widths
    (semanticRound : Fin 10) (oodSample : Fin 2)
    (relationRound : Fin 4) :
    absorbFrame (.absorbSemanticRound semanticRound) = some ⟨48, 433⟩ ∧
      absorbFrame (.absorbPointClaims3x29) = some ⟨49, 3 * 29 * 16⟩ ∧
      absorbFrame (.absorbOodValue oodSample) = some ⟨51, 17⟩ ∧
      absorbFrame (.absorbRelationRound relationRound) = some ⟨52, 97⟩ ∧
      absorbFrame .absorbFinal256 = some ⟨53, 256 * 16⟩ ∧
      absorbFrame .absorbQueryBatchChallengeDomain = some ⟨55, 0⟩ ∧
      absorbFrame .absorbQueryBatchClaim = some ⟨56, 16⟩ := by
  norm_num [absorbFrame]

def isChallengeOperation : ExecutionOperation → Bool
  | .squeezeLambda | .squeezeChi | .squeezeTheta | .squeezeMu |
      .squeezeEtaNonzero | .squeezeGammaNonzero | .squeezeKappaNonzero |
      .squeezeQueryBatchRhoNonzero => true
  | .squeezeZerocheckCoordinate _ | .squeezeSemanticRound _ |
      .squeezeCirclePoint _ | .squeezeOodMix _ | .squeezeRelationAlpha _ => true
  | _ => false

def semanticRoundOperations : List ExecutionOperation :=
  (List.ofFn fun round : Fin 10 =>
    [.absorbSemanticRound round, .squeezeSemanticRound round]).flatten

def oodOperations : List ExecutionOperation :=
  (List.ofFn fun sample : Fin 2 =>
    [.squeezeCirclePoint sample, .absorbOodValue sample,
      .squeezeOodMix sample]).flatten

def laterRelationOperations : List ExecutionOperation :=
  (List.ofFn fun later : Fin 3 =>
    let round : Fin 4 := ⟨later.val + 1, by omega⟩
    [.absorbRelationRound round, .squeezeRelationAlpha round,
      .foldRelationWeights round, .foldDisclosedFinal later]).flatten

/-- The exact successful control-flow order through the fixed transcript and
relation driver. Query-candidate retries follow this list and are modeled
separately because their accepted length is data-dependent. -/
def acceptedExecutionGrammar : List ExecutionOperation :=
  [.absorbProfile,
    .absorbCircleBasis,
    .absorbDeploymentContext,
    .absorbStatement,
    .absorbHidingPrecommit,
    .absorbC1RootAndSalt,
    .squeezeLambda,
    .squeezeChi,
    .absorbC2RootAndSalt,
    .absorbConstraintRegistry,
    .absorbHelperSum,
    .squeezeTheta] ++
  (List.ofFn fun coordinate : Fin 10 =>
    .squeezeZerocheckCoordinate coordinate) ++
  [.squeezeMu,
    .absorbMaskedInitialClaim,
    .squeezeEtaNonzero] ++
  semanticRoundOperations ++
  [.absorbPointClaims3x29,
    .checkSemanticTerminal,
    .checkWork .batch,
    .absorbWork .batch,
    .squeezeGammaNonzero,
    .absorbInactiveClaim,
    .squeezeKappaNonzero] ++
  oodOperations ++
  [.absorbRelationRound 0,
    .checkWork .fold,
    .absorbWork .fold,
    .squeezeRelationAlpha 0,
    .foldRelationWeights 0,
    .absorbFinal256,
    .checkWork .final,
    .absorbWork .final,
    .deriveFirstCompactQueries,
    .adoptSelectedQueryTranscript,
    .checkFrontierCounts,
    .absorbQueryBatchChallengeDomain,
    .squeezeQueryBatchRhoNonzero,
    .authenticateAndFoldQueries,
    .addQueryBatchWeightsAndClaim,
    .absorbQueryBatchClaim] ++
  laterRelationOperations ++
  [.checkRelationTerminal]

theorem accepted_execution_grammar_length :
    acceptedExecutionGrammar.length = 87 := by
  decide

theorem accepted_execution_grammar_has_no_duplicate_slots :
    acceptedExecutionGrammar.Nodup := by
  decide

/-- Thirty-six typed field/circle samples occur outside query decoding: the
original thirty-five plus the fresh nonzero query-batching challenge.  The
bounded q16 decoder consumes a data-dependent number of hash blocks in each
attempted candidate clone. -/
theorem accepted_execution_has_exactly_thirty_six_challenges :
    (acceptedExecutionGrammar.filter isChallengeOperation).length = 36 := by
  decide

def checkedWorkOrder : List WorkStage :=
  acceptedExecutionGrammar.filterMap fun operation =>
    match operation with
    | .checkWork stage => some stage
    | _ => none

def absorbedWorkOrder : List WorkStage :=
  acceptedExecutionGrammar.filterMap fun operation =>
    match operation with
    | .absorbWork stage => some stage
    | _ => none

theorem every_work_stage_is_checked_and_absorbed_once_in_order :
    checkedWorkOrder = [.batch, .fold, .final] ∧
      absorbedWorkOrder = [.batch, .fold, .final] := by
  decide

theorem terminal_precedes_batch_work_and_gamma :
    acceptedExecutionGrammar.idxOf .checkSemanticTerminal <
        acceptedExecutionGrammar.idxOf (.checkWork .batch) ∧
      acceptedExecutionGrammar.idxOf (.checkWork .batch) <
        acceptedExecutionGrammar.idxOf .squeezeGammaNonzero := by
  decide

theorem final256_is_after_alpha0_and_before_relation_round1 :
    acceptedExecutionGrammar.idxOf (.squeezeRelationAlpha 0) <
        acceptedExecutionGrammar.idxOf .absorbFinal256 ∧
      acceptedExecutionGrammar.idxOf .absorbFinal256 <
        acceptedExecutionGrammar.idxOf (.absorbRelationRound 1) := by
  decide

theorem query_batch_is_after_final_work_and_before_relation_round1 :
    acceptedExecutionGrammar.idxOf (.absorbWork .final) <
        acceptedExecutionGrammar.idxOf .deriveFirstCompactQueries ∧
      acceptedExecutionGrammar.idxOf .deriveFirstCompactQueries <
        acceptedExecutionGrammar.idxOf .adoptSelectedQueryTranscript ∧
      acceptedExecutionGrammar.idxOf .adoptSelectedQueryTranscript <
        acceptedExecutionGrammar.idxOf .checkFrontierCounts ∧
      acceptedExecutionGrammar.idxOf .checkFrontierCounts <
        acceptedExecutionGrammar.idxOf .squeezeQueryBatchRhoNonzero ∧
      acceptedExecutionGrammar.idxOf .squeezeQueryBatchRhoNonzero <
        acceptedExecutionGrammar.idxOf .authenticateAndFoldQueries ∧
      acceptedExecutionGrammar.idxOf .authenticateAndFoldQueries <
        acceptedExecutionGrammar.idxOf .absorbQueryBatchClaim ∧
      acceptedExecutionGrammar.idxOf .absorbQueryBatchClaim <
        acceptedExecutionGrammar.idxOf (.absorbRelationRound 1) := by
  decide

theorem only_first_relation_round_has_fold_work :
    acceptedExecutionGrammar.idxOf (.absorbRelationRound 0) <
        acceptedExecutionGrammar.idxOf (.checkWork .fold) ∧
      acceptedExecutionGrammar.idxOf (.checkWork .fold) <
        acceptedExecutionGrammar.idxOf (.squeezeRelationAlpha 0) := by
  decide

/-! ## Public root-salt framing and compact retries -/

inductive RootSaltInput where
  | domain
  | profile
  | programId
  | releaseBinding
  | statementDigest
  | attemptId
  | treeTag
  deriving DecidableEq

def rootSaltInputOrder : List RootSaltInput :=
  [.domain, .profile, .programId, .releaseBinding, .statementDigest,
    .attemptId, .treeTag]

theorem exact_root_salt_input_order :
    rootSaltInputOrder.length = 7 ∧ rootSaltInputOrder.Nodup := by
  decide

structure QueryCandidateBinding where
  selector : Fin 3
  counter : Fin 8

def QueryCandidateBinding.bytes (binding : QueryCandidateBinding) : List Nat :=
  [binding.selector.val, binding.counter.val]

theorem query_candidate_binding_has_exact_width
    (binding : QueryCandidateBinding) :
    binding.bytes.length = 2 := by
  rfl

def queryCandidateAbsorbFrame : AbsorbFrame := ⟨54, 2⟩

theorem exact_query_candidate_absorb_frame :
    queryCandidateAbsorbFrame = ⟨54, 2⟩ := by
  rfl

/-! ## Audit -/

#print axioms exact_profile_binding
#print axioms exact_fixed_field_offsets
#print axioms exact_fixed_packed_dimensions
#print axioms exact_complete_body_dimensions
#print axioms point_claim_field_index_injective
#print axioms every_fixed_field_is_consumed_once
#print axioms terminal_excludes_exactly_d_lane
#print axioms reconstructed_semantic_linear_has_exact_boundary
#print axioms reconstructed_relation_quartic_has_exact_boundary
#print axioms accepted_execution_grammar_has_no_duplicate_slots
#print axioms every_work_stage_is_checked_and_absorbed_once_in_order
#print axioms terminal_precedes_batch_work_and_gamma
#print axioms final256_is_after_alpha0_and_before_relation_round1
#print axioms query_batch_is_after_final_work_and_before_relation_round1

end AspisV6TranscriptRelationGrammar
