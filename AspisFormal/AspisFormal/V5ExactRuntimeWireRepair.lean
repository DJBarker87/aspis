import Mathlib

/-!
# Exact repaired mode-9 wire grammar

This file models the runtime grammar after removing the retired width-26 C1
comparison span.  It proves the fixed parser-field partition, the exact current
runtime-sized Merkle suffix, serializer/parser round-trip, and rejection by
length of the former, truncated, and appended layouts.  Cryptographic validity
and Rust correspondence are deliberately outside this byte-level model.
-/

namespace AspisFormal.V5ExactRuntimeWireRepair

abbrev Byte := Fin 256

def queryCount : Nat := 18
def leafSaltBytes : Nat := 32
def candidateC1ValueBytes : Nat := 256
def c2ValueBytes : Nat := 192
def laterValueBytes : Nat := 64
def retiredProductionC1ValueBytes : Nat := 416

def candidateC1RecordBytes : Nat := candidateC1ValueBytes + leafSaltBytes
def c2RecordBytes : Nat := c2ValueBytes + leafSaltBytes
def retiredProductionC1RecordBytes : Nat := retiredProductionC1ValueBytes + leafSaltBytes
def retiredProductionC1SpanBytes : Nat := queryCount * retiredProductionC1RecordBytes

def magicOffset : Nat := 0
def gammaOffset : Nat := 8
def candidateC1Offset : Nat := 24
def c2Offset : Nat := 5208
def relationScalesOffset : Nat := 9240
def relationPointsOffset : Nat := 9288
def relationClaimsOffset : Nat := 9768
def relationAlphasOffset : Nat := 10984
def relationFinalOffset : Nat := 11048
def wirePrefixOffset : Nat := 11112
def atomicContextOffset : Nat := 17535
def privateRootsOffset : Nat := 17975
def finalCoefficientsOffset : Nat := 18135
def relationStressOffset : Nat := 18199
def finalNonceOffset : Nat := 19127
def querySelectorOffset : Nat := 19135
def repairedFixedBytes : Nat := 19136

theorem retired_production_c1_span_is_8064 : retiredProductionC1SpanBytes = 8064 := by
  norm_num [retiredProductionC1SpanBytes, retiredProductionC1RecordBytes,
    retiredProductionC1ValueBytes, leafSaltBytes, queryCount]

theorem repaired_offsets_are_contiguous :
    gammaOffset = magicOffset + 8 ∧
    candidateC1Offset = gammaOffset + 16 ∧
    c2Offset = candidateC1Offset + queryCount * candidateC1RecordBytes ∧
    relationScalesOffset = c2Offset + queryCount * c2RecordBytes ∧
    relationPointsOffset = relationScalesOffset + 48 ∧
    relationClaimsOffset = relationPointsOffset + 480 ∧
    relationAlphasOffset = relationClaimsOffset + 1216 ∧
    relationFinalOffset = relationAlphasOffset + 64 ∧
    wirePrefixOffset = relationFinalOffset + 64 ∧
    atomicContextOffset = wirePrefixOffset + 6423 ∧
    privateRootsOffset = atomicContextOffset + 440 ∧
    finalCoefficientsOffset = privateRootsOffset + 160 ∧
    relationStressOffset = finalCoefficientsOffset + 64 ∧
    finalNonceOffset = relationStressOffset + 928 ∧
    querySelectorOffset = finalNonceOffset + 8 ∧
    repairedFixedBytes = querySelectorOffset + 1 := by
  norm_num [magicOffset, gammaOffset, candidateC1Offset, c2Offset,
    relationScalesOffset, relationPointsOffset, relationClaimsOffset,
    relationAlphasOffset, relationFinalOffset, wirePrefixOffset,
    atomicContextOffset, privateRootsOffset, finalCoefficientsOffset,
    relationStressOffset, finalNonceOffset, querySelectorOffset,
    repairedFixedBytes, queryCount, candidateC1RecordBytes, c2RecordBytes,
    candidateC1ValueBytes, c2ValueBytes, leafSaltBytes]

inductive FixedSpan where
  | magic
  | gamma
  | candidateC1
  | c2
  | relationScales
  | relationPoints
  | relationClaims
  | relationAlphas
  | relationFinal
  | wirePrefix
  | atomicContext
  | privateRoots
  | finalCoefficients
  | relationStress
  | finalNonce
  | querySelector
  deriving DecidableEq, Fintype

def FixedSpan.start : FixedSpan → Nat
  | .magic => magicOffset
  | .gamma => gammaOffset
  | .candidateC1 => candidateC1Offset
  | .c2 => c2Offset
  | .relationScales => relationScalesOffset
  | .relationPoints => relationPointsOffset
  | .relationClaims => relationClaimsOffset
  | .relationAlphas => relationAlphasOffset
  | .relationFinal => relationFinalOffset
  | .wirePrefix => wirePrefixOffset
  | .atomicContext => atomicContextOffset
  | .privateRoots => privateRootsOffset
  | .finalCoefficients => finalCoefficientsOffset
  | .relationStress => relationStressOffset
  | .finalNonce => finalNonceOffset
  | .querySelector => querySelectorOffset

def FixedSpan.stop : FixedSpan → Nat
  | .magic => gammaOffset
  | .gamma => candidateC1Offset
  | .candidateC1 => c2Offset
  | .c2 => relationScalesOffset
  | .relationScales => relationPointsOffset
  | .relationPoints => relationClaimsOffset
  | .relationClaims => relationAlphasOffset
  | .relationAlphas => relationFinalOffset
  | .relationFinal => wirePrefixOffset
  | .wirePrefix => atomicContextOffset
  | .atomicContext => privateRootsOffset
  | .privateRoots => finalCoefficientsOffset
  | .finalCoefficients => relationStressOffset
  | .relationStress => finalNonceOffset
  | .finalNonce => querySelectorOffset
  | .querySelector => repairedFixedBytes

def fixedSpanAt (offset : Nat) : FixedSpan :=
  if offset < gammaOffset then .magic
  else if offset < candidateC1Offset then .gamma
  else if offset < c2Offset then .candidateC1
  else if offset < relationScalesOffset then .c2
  else if offset < relationPointsOffset then .relationScales
  else if offset < relationClaimsOffset then .relationPoints
  else if offset < relationAlphasOffset then .relationClaims
  else if offset < relationFinalOffset then .relationAlphas
  else if offset < wirePrefixOffset then .relationFinal
  else if offset < atomicContextOffset then .wirePrefix
  else if offset < privateRootsOffset then .atomicContext
  else if offset < finalCoefficientsOffset then .privateRoots
  else if offset < relationStressOffset then .finalCoefficients
  else if offset < finalNonceOffset then .relationStress
  else if offset < querySelectorOffset then .finalNonce
  else .querySelector

theorem fixed_span_total (offset : Nat) (h : offset < repairedFixedBytes) :
    (fixedSpanAt offset).start ≤ offset ∧ offset < (fixedSpanAt offset).stop := by
  by_cases h0 : offset < gammaOffset
  · simp [fixedSpanAt, h0, FixedSpan.start, FixedSpan.stop, magicOffset]
  · by_cases h1 : offset < candidateC1Offset
    · simp [fixedSpanAt, h0, h1, FixedSpan.start, FixedSpan.stop]
      omega
    · by_cases h2 : offset < c2Offset
      · simp [fixedSpanAt, h0, h1, h2, FixedSpan.start, FixedSpan.stop]
        omega
      · by_cases h3 : offset < relationScalesOffset
        · simp [fixedSpanAt, h0, h1, h2, h3, FixedSpan.start, FixedSpan.stop]
          omega
        · by_cases h4 : offset < relationPointsOffset
          · simp [fixedSpanAt, h0, h1, h2, h3, h4, FixedSpan.start, FixedSpan.stop]
            omega
          · by_cases h5 : offset < relationClaimsOffset
            · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, FixedSpan.start, FixedSpan.stop]
              omega
            · by_cases h6 : offset < relationAlphasOffset
              · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6,
                  FixedSpan.start, FixedSpan.stop]
                omega
              · by_cases h7 : offset < relationFinalOffset
                · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6, h7,
                    FixedSpan.start, FixedSpan.stop]
                  omega
                · by_cases h8 : offset < wirePrefixOffset
                  · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6, h7, h8,
                      FixedSpan.start, FixedSpan.stop]
                    omega
                  · by_cases h9 : offset < atomicContextOffset
                    · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
                        FixedSpan.start, FixedSpan.stop]
                      omega
                    · by_cases h10 : offset < privateRootsOffset
                      · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                          FixedSpan.start, FixedSpan.stop]
                        omega
                      · by_cases h11 : offset < finalCoefficientsOffset
                        · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                            h11, FixedSpan.start, FixedSpan.stop]
                          omega
                        · by_cases h12 : offset < relationStressOffset
                          · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                              h11, h12, FixedSpan.start, FixedSpan.stop]
                            omega
                          · by_cases h13 : offset < finalNonceOffset
                            · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                                h11, h12, h13, FixedSpan.start, FixedSpan.stop]
                              omega
                            · by_cases h14 : offset < querySelectorOffset
                              · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
                                  h10, h11, h12, h13, h14, FixedSpan.start, FixedSpan.stop]
                                omega
                              · simp [fixedSpanAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
                                  h10, h11, h12, h13, h14, FixedSpan.start, FixedSpan.stop]
                                omega

theorem fixed_span_pairwise_disjoint :
    ∀ first second : FixedSpan, first ≠ second →
      first.stop ≤ second.start ∨ second.stop ≤ first.start := by
  decide

theorem fixed_span_unique (offset : Nat) (h : offset < repairedFixedBytes)
    (span : FixedSpan) (hs : span.start ≤ offset ∧ offset < span.stop) :
    span = fixedSpanAt offset := by
  by_contra hne
  have hd := fixed_span_pairwise_disjoint span (fixedSpanAt offset) hne
  have hc := fixed_span_total offset h
  omega

theorem every_fixed_byte_has_exactly_one_parser_span (offset : Nat)
    (h : offset < repairedFixedBytes) :
    ∃! span : FixedSpan, span.start ≤ offset ∧ offset < span.stop := by
  refine ⟨fixedSpanAt offset, fixed_span_total offset h, ?_⟩
  intro span hs
  exact fixed_span_unique offset h span hs

inductive SuffixSection where
  | c1
  | c2
  | later1
  | later2
  | later3
  deriving DecidableEq, Fintype

/-! ## Runtime-sized five-section suffix -/

/-- The five record widths are protocol constants.  Only record and Merkle
frontier counts vary with the deduplicated q18 schedule. -/
def SuffixSection.valueBytes : SuffixSection → Nat
  | .c1 => candidateC1ValueBytes
  | .c2 => c2ValueBytes
  | .later1 | .later2 | .later3 => laterValueBytes

/-- Runtime shape of the private-opening suffix.  Equality of this structure
includes both all five record counts and all five frontier counts. -/
structure RuntimeShape where
  recordCount : SuffixSection → Nat
  frontierCount : SuffixSection → Nat
  deriving DecidableEq

/-- One canonical private-opening section is
`count_u16 || (value || salt32)^count || frontier_count_u32 || frontier32*`. -/
def runtimeSectionBytes (shape : RuntimeShape) (part : SuffixSection) : Nat :=
  2 + shape.recordCount part * (part.valueBytes + leafSaltBytes) +
    4 + shape.frontierCount part * 32

def RuntimeShape.recordCounts (shape : RuntimeShape) : List Nat :=
  [shape.recordCount .c1, shape.recordCount .c2,
    shape.recordCount .later1, shape.recordCount .later2,
    shape.recordCount .later3]

def RuntimeShape.frontierCounts (shape : RuntimeShape) : List Nat :=
  [shape.frontierCount .c1, shape.frontierCount .c2,
    shape.frontierCount .later1, shape.frontierCount .later2,
    shape.frontierCount .later3]

def RuntimeShape.sectionBytes (shape : RuntimeShape) : List Nat :=
  [runtimeSectionBytes shape .c1, runtimeSectionBytes shape .c2,
    runtimeSectionBytes shape .later1, runtimeSectionBytes shape .later2,
    runtimeSectionBytes shape .later3]

/-- Total suffix length for an arbitrary runtime-derived shape. -/
def runtimeSuffixBytes (shape : RuntimeShape) : Nat :=
  runtimeSectionBytes shape .c1 + runtimeSectionBytes shape .c2 +
    runtimeSectionBytes shape .later1 + runtimeSectionBytes shape .later2 +
    runtimeSectionBytes shape .later3

def runtimeRepairedProofBytes (shape : RuntimeShape) : Nat :=
  repairedFixedBytes + runtimeSuffixBytes shape

def formerFixedBytes : Nat := repairedFixedBytes + retiredProductionC1SpanBytes

def runtimeFormerProofBytes (shape : RuntimeShape) : Nat :=
  formerFixedBytes + runtimeSuffixBytes shape

def runtimeSectionStart (shape : RuntimeShape) : SuffixSection → Nat
  | .c1 => 0
  | .c2 => runtimeSectionBytes shape .c1
  | .later1 => runtimeSectionBytes shape .c1 + runtimeSectionBytes shape .c2
  | .later2 => runtimeSectionBytes shape .c1 + runtimeSectionBytes shape .c2 +
      runtimeSectionBytes shape .later1
  | .later3 => runtimeSectionBytes shape .c1 + runtimeSectionBytes shape .c2 +
      runtimeSectionBytes shape .later1 + runtimeSectionBytes shape .later2

def runtimeSectionStop (shape : RuntimeShape) (part : SuffixSection) : Nat :=
  runtimeSectionStart shape part + runtimeSectionBytes shape part

theorem runtime_section_bytes_positive (shape : RuntimeShape)
    (part : SuffixSection) : 0 < runtimeSectionBytes shape part := by
  simp [runtimeSectionBytes]

theorem runtime_suffix_offsets_are_cumulative (shape : RuntimeShape) :
    runtimeSectionStart shape .c1 = 0 ∧
    runtimeSectionStop shape .c1 = runtimeSectionStart shape .c2 ∧
    runtimeSectionStop shape .c2 = runtimeSectionStart shape .later1 ∧
    runtimeSectionStop shape .later1 = runtimeSectionStart shape .later2 ∧
    runtimeSectionStop shape .later2 = runtimeSectionStart shape .later3 ∧
    runtimeSectionStop shape .later3 = runtimeSuffixBytes shape := by
  simp [runtimeSectionStart, runtimeSectionStop, runtimeSuffixBytes]

def runtimeSuffixSectionAt (shape : RuntimeShape) (offset : Nat) : SuffixSection :=
  if offset < runtimeSectionStop shape .c1 then .c1
  else if offset < runtimeSectionStop shape .c2 then .c2
  else if offset < runtimeSectionStop shape .later1 then .later1
  else if offset < runtimeSectionStop shape .later2 then .later2
  else .later3

theorem runtime_suffix_section_total (shape : RuntimeShape) (offset : Nat)
    (h : offset < runtimeSuffixBytes shape) :
    runtimeSectionStart shape (runtimeSuffixSectionAt shape offset) ≤ offset ∧
      offset < runtimeSectionStop shape (runtimeSuffixSectionAt shape offset) := by
  by_cases h0 : offset < runtimeSectionStop shape .c1
  · rw [runtimeSuffixSectionAt, if_pos h0]
    constructor
    · simp [runtimeSectionStart]
    · simpa [runtimeSectionStart, runtimeSectionStop] using h0
  · by_cases h1 : offset < runtimeSectionStop shape .c2
    · rw [runtimeSuffixSectionAt, if_neg h0, if_pos h1]
      simp [runtimeSectionStart, runtimeSectionStop] at h0 h1 ⊢
      omega
    · by_cases h2 : offset < runtimeSectionStop shape .later1
      · rw [runtimeSuffixSectionAt, if_neg h0, if_neg h1, if_pos h2]
        simp [runtimeSectionStart, runtimeSectionStop] at h0 h1 h2 ⊢
        omega
      · by_cases h3 : offset < runtimeSectionStop shape .later2
        · rw [runtimeSuffixSectionAt, if_neg h0, if_neg h1, if_neg h2,
            if_pos h3]
          simp [runtimeSectionStart, runtimeSectionStop] at h0 h1 h2 h3 ⊢
          omega
        · rw [runtimeSuffixSectionAt, if_neg h0, if_neg h1, if_neg h2,
            if_neg h3]
          simp [runtimeSectionStart, runtimeSectionStop] at h0 h1 h2 h3 ⊢
          simp [runtimeSuffixBytes] at h
          omega

theorem runtime_suffix_sections_pairwise_disjoint (shape : RuntimeShape) :
    ∀ first second : SuffixSection, first ≠ second →
      runtimeSectionStop shape first ≤ runtimeSectionStart shape second ∨
        runtimeSectionStop shape second ≤ runtimeSectionStart shape first := by
  intro first second hne
  fin_cases first <;> fin_cases second <;>
    simp_all [runtimeSectionStart, runtimeSectionStop] <;> omega

theorem runtime_suffix_section_unique (shape : RuntimeShape) (offset : Nat)
    (h : offset < runtimeSuffixBytes shape) (part : SuffixSection)
    (hs : runtimeSectionStart shape part ≤ offset ∧
      offset < runtimeSectionStop shape part) :
    part = runtimeSuffixSectionAt shape offset := by
  by_contra hne
  have hd := runtime_suffix_sections_pairwise_disjoint shape part
    (runtimeSuffixSectionAt shape offset) hne
  have hc := runtime_suffix_section_total shape offset h
  omega

theorem every_runtime_suffix_byte_has_exactly_one_section
    (shape : RuntimeShape) (offset : Nat) (h : offset < runtimeSuffixBytes shape) :
    ∃! part : SuffixSection,
      runtimeSectionStart shape part ≤ offset ∧
        offset < runtimeSectionStop shape part := by
  refine ⟨runtimeSuffixSectionAt shape offset,
    runtime_suffix_section_total shape offset h, ?_⟩
  intro part hs
  exact runtime_suffix_section_unique shape offset h part hs

/-! ## Exact whole-body span coverage -/

inductive RuntimeSpan where
  | fixed : FixedSpan → RuntimeSpan
  | suffix : SuffixSection → RuntimeSpan
  deriving DecidableEq, Fintype

def RuntimeSpan.start (shape : RuntimeShape) : RuntimeSpan → Nat
  | .fixed span => span.start
  | .suffix part => repairedFixedBytes + runtimeSectionStart shape part

def RuntimeSpan.stop (shape : RuntimeShape) : RuntimeSpan → Nat
  | .fixed span => span.stop
  | .suffix part => repairedFixedBytes + runtimeSectionStop shape part

def runtimeSpanAt (shape : RuntimeShape) (offset : Nat) : RuntimeSpan :=
  if offset < repairedFixedBytes then .fixed (fixedSpanAt offset)
  else .suffix (runtimeSuffixSectionAt shape (offset - repairedFixedBytes))

theorem fixed_span_stop_le_repairedFixedBytes (span : FixedSpan) :
    span.stop ≤ repairedFixedBytes := by
  fin_cases span <;> decide

theorem runtime_span_total (shape : RuntimeShape) (offset : Nat)
    (h : offset < runtimeRepairedProofBytes shape) :
    (runtimeSpanAt shape offset).start shape ≤ offset ∧
      offset < (runtimeSpanAt shape offset).stop shape := by
  by_cases hfixed : offset < repairedFixedBytes
  · simp [runtimeSpanAt, hfixed, RuntimeSpan.start, RuntimeSpan.stop]
    exact fixed_span_total offset hfixed
  · have hsuffix : offset - repairedFixedBytes < runtimeSuffixBytes shape := by
      simp [runtimeRepairedProofBytes] at h
      omega
    have hs := runtime_suffix_section_total shape
      (offset - repairedFixedBytes) hsuffix
    simp [runtimeSpanAt, hfixed, RuntimeSpan.start, RuntimeSpan.stop]
    omega

theorem runtime_spans_pairwise_disjoint (shape : RuntimeShape) :
    ∀ first second : RuntimeSpan, first ≠ second →
      first.stop shape ≤ second.start shape ∨
        second.stop shape ≤ first.start shape := by
  intro first second hne
  cases first with
  | fixed first =>
      cases second with
      | fixed second =>
          simp only [RuntimeSpan.stop, RuntimeSpan.start]
          exact fixed_span_pairwise_disjoint first second (by simpa using hne)
      | suffix second =>
          left
          simp only [RuntimeSpan.stop, RuntimeSpan.start]
          have hstop := fixed_span_stop_le_repairedFixedBytes first
          omega
  | suffix first =>
      cases second with
      | fixed second =>
          right
          simp only [RuntimeSpan.stop, RuntimeSpan.start]
          have hstop := fixed_span_stop_le_repairedFixedBytes second
          omega
      | suffix second =>
          simp only [RuntimeSpan.stop, RuntimeSpan.start]
          have hd := runtime_suffix_sections_pairwise_disjoint shape first second
            (by simpa using hne)
          omega

theorem runtime_span_unique (shape : RuntimeShape) (offset : Nat)
    (h : offset < runtimeRepairedProofBytes shape) (span : RuntimeSpan)
    (hs : span.start shape ≤ offset ∧ offset < span.stop shape) :
    span = runtimeSpanAt shape offset := by
  by_contra hne
  have hd := runtime_spans_pairwise_disjoint shape span
    (runtimeSpanAt shape offset) hne
  have hc := runtime_span_total shape offset h
  omega

theorem every_runtime_body_byte_has_exactly_one_span
    (shape : RuntimeShape) (offset : Nat)
    (h : offset < runtimeRepairedProofBytes shape) :
    ∃! span : RuntimeSpan,
      span.start shape ≤ offset ∧ offset < span.stop shape := by
  refine ⟨runtimeSpanAt shape offset, runtime_span_total shape offset h, ?_⟩
  intro span hs
  exact runtime_span_unique shape offset h span hs

/-! ## Runtime-size regression points and the Rust correspondence boundary -/

/-- Accepted runtime q18 schedules are 18 distinct fibre indices. -/
abbrev Q18Schedule := Fin queryCount → Fin 131072

/-- Exact equality of Rust's query-derived record/frontier counts and a supplied
mathematical shape function.  This is a named executable-correspondence premise;
no theorem below claims to derive Rust's Merkle frontier algorithm. -/
def ExactRustQueryToRuntimeShapeCorrespondence
    (rustShape modelShape : Q18Schedule → RuntimeShape) : Prop :=
  ∀ queries, Function.Injective queries → rustShape queries = modelShape queries

/-- Concrete distinct regression schedule `q = 0, ..., 17`. -/
def zeroToSeventeenQ18 : Q18Schedule :=
  fun query => ⟨query, by
    have h := query.isLt
    simp only [queryCount] at h
    omega⟩

theorem zeroToSeventeenQ18_injective : Function.Injective zeroToSeventeenQ18 := by
  intro left right equal
  apply Fin.ext
  simpa [zeroToSeventeenQ18] using congrArg Fin.val equal

/-- Cardinality after the runtime's `q >> shift` deduplication rule. -/
def shiftedZeroToSeventeenCount (shift : Nat) : Nat :=
  ((Finset.univ : Finset (Fin queryCount)).image
    (fun query => ((zeroToSeventeenQ18 query : Fin 131072) : Nat) / 2 ^ shift)).card

theorem zeroToSeventeen_shifted_record_counts :
    [shiftedZeroToSeventeenCount 0, shiftedZeroToSeventeenCount 0,
      shiftedZeroToSeventeenCount 2, shiftedZeroToSeventeenCount 4,
      shiftedZeroToSeventeenCount 6] = [18, 18, 5, 2, 1] := by
  decide

/-- Regression shape for distinct q18 `0..17`.  The frontier counts are the
canonical Merkle-frontier regression values; their equality to Rust remains
inside `ExactRustQueryToRuntimeShapeCorrespondence`. -/
def zeroToSeventeenRuntimeShape : RuntimeShape where
  recordCount
    | .c1 | .c2 => 18
    | .later1 => 5
    | .later2 => 2
    | .later3 => 1
  frontierCount
    | .c1 | .c2 => 23
    | .later1 => 21
    | .later2 => 18
    | .later3 => 16

theorem zeroToSeventeen_shape_counts :
    zeroToSeventeenRuntimeShape.recordCounts = [18, 18, 5, 2, 1] ∧
      zeroToSeventeenRuntimeShape.frontierCounts = [23, 23, 21, 18, 16] := by
  decide

theorem zeroToSeventeen_section_bytes :
    zeroToSeventeenRuntimeShape.sectionBytes = [5926, 4774, 1158, 774, 614] := by
  norm_num [RuntimeShape.sectionBytes, runtimeSectionBytes,
    zeroToSeventeenRuntimeShape, SuffixSection.valueBytes,
    candidateC1ValueBytes, c2ValueBytes, laterValueBytes, leafSaltBytes]

theorem zeroToSeventeen_runtime_suffix_is_13246 :
    runtimeSuffixBytes zeroToSeventeenRuntimeShape = 13246 := by
  norm_num [runtimeSuffixBytes, runtimeSectionBytes, zeroToSeventeenRuntimeShape,
    SuffixSection.valueBytes, candidateC1ValueBytes, c2ValueBytes,
    laterValueBytes, leafSaltBytes]

theorem zeroToSeventeen_runtime_body_is_32382 :
    runtimeRepairedProofBytes zeroToSeventeenRuntimeShape = 32382 := by
  norm_num [runtimeRepairedProofBytes, repairedFixedBytes, runtimeSuffixBytes,
    runtimeSectionBytes, zeroToSeventeenRuntimeShape, SuffixSection.valueBytes,
    candidateC1ValueBytes, c2ValueBytes, laterValueBytes, leafSaltBytes]

/-! ### The 75,358-byte value is one frozen fixture, not the runtime grammar -/

def currentFixtureRuntimeShape : RuntimeShape where
  recordCount _ := 18
  frontierCount
    | .c1 | .c2 => 326
    | .later1 => 272
    | .later2 => 218
    | .later3 => 164

def currentFixtureRuntimeSuffixBytes : Nat :=
  runtimeSuffixBytes currentFixtureRuntimeShape

def currentFixtureRepairedProofBytes : Nat :=
  runtimeRepairedProofBytes currentFixtureRuntimeShape

def formerFixtureProofBytes : Nat :=
  runtimeFormerProofBytes currentFixtureRuntimeShape

theorem current_fixture_section_sizes_are_exact :
    currentFixtureRuntimeShape.sectionBytes = [15622, 14470, 10438, 8710, 6982] := by
  norm_num [RuntimeShape.sectionBytes, runtimeSectionBytes,
    currentFixtureRuntimeShape, SuffixSection.valueBytes, candidateC1ValueBytes,
    c2ValueBytes, laterValueBytes, leafSaltBytes]

theorem current_fixture_runtime_suffix_is_56222 :
    currentFixtureRuntimeSuffixBytes = 56222 := by
  norm_num [currentFixtureRuntimeSuffixBytes, runtimeSuffixBytes,
    runtimeSectionBytes, currentFixtureRuntimeShape, SuffixSection.valueBytes,
    candidateC1ValueBytes, c2ValueBytes, laterValueBytes, leafSaltBytes]

/-- The historical 75,358-byte statement is explicitly fixture-only. -/
theorem current_fixture_repaired_proof_is_75358 :
    currentFixtureRepairedProofBytes = 75358 := by
  norm_num [currentFixtureRepairedProofBytes, runtimeRepairedProofBytes,
    repairedFixedBytes, currentFixtureRuntimeSuffixBytes, runtimeSuffixBytes,
    runtimeSectionBytes, currentFixtureRuntimeShape, SuffixSection.valueBytes,
    candidateC1ValueBytes, c2ValueBytes, laterValueBytes, leafSaltBytes]

theorem former_fixture_proof_is_83422 : formerFixtureProofBytes = 83422 := by
  norm_num [formerFixtureProofBytes, runtimeFormerProofBytes, formerFixedBytes,
    repairedFixedBytes, retiredProductionC1SpanBytes,
    retiredProductionC1RecordBytes, retiredProductionC1ValueBytes, queryCount,
    runtimeSuffixBytes, runtimeSectionBytes, currentFixtureRuntimeShape,
    SuffixSection.valueBytes, candidateC1ValueBytes, c2ValueBytes,
    laterValueBytes, leafSaltBytes]

/-! ## The repair delta is shape-independent -/

theorem runtime_repair_removes_exactly_8064_bytes (shape : RuntimeShape) :
    runtimeFormerProofBytes shape - runtimeRepairedProofBytes shape =
      retiredProductionC1SpanBytes := by
  simp only [runtimeFormerProofBytes, runtimeRepairedProofBytes, formerFixedBytes]
  rw [retired_production_c1_span_is_8064]
  omega

theorem runtime_repair_signed_delta_is_negative_8064 (shape : RuntimeShape) :
    (runtimeRepairedProofBytes shape : Int) - runtimeFormerProofBytes shape = -8064 := by
  have hformer : runtimeFormerProofBytes shape =
      runtimeRepairedProofBytes shape + 8064 := by
    simp only [runtimeFormerProofBytes, runtimeRepairedProofBytes, formerFixedBytes]
    rw [retired_production_c1_span_is_8064]
    omega
  rw [hformer]
  push_cast
  ring

abbrev ExactBytes (n : Nat) := { bytes : List Byte // bytes.length = n }

def serializeExact {n : Nat} (wire : ExactBytes n) : List Byte := wire.1

def parseExact (n : Nat) (bytes : List Byte) : Option (ExactBytes n) :=
  if h : bytes.length = n then some ⟨bytes, h⟩ else none

theorem parse_serialize_roundtrip {n : Nat} (wire : ExactBytes n) :
    parseExact n (serializeExact wire) = some wire := by
  simp [parseExact, serializeExact]

def ExactRustMode9SerializerParserCorrespondence (n : Nat)
    (rustSerialize : ExactBytes n → List Byte)
    (rustParse : List Byte → Option (ExactBytes n)) : Prop :=
  (∀ wire, rustSerialize wire = serializeExact wire) ∧
    (∀ bytes, rustParse bytes = parseExact n bytes)

theorem rust_roundtrip_of_named_correspondence {n : Nat}
    (rustSerialize : ExactBytes n → List Byte)
    (rustParse : List Byte → Option (ExactBytes n))
    (h : ExactRustMode9SerializerParserCorrespondence n rustSerialize rustParse)
    (wire : ExactBytes n) : rustParse (rustSerialize wire) = some wire := by
  rw [h.2, h.1]
  exact parse_serialize_roundtrip wire

theorem successful_parse_serializes_identically {n : Nat} (bytes : List Byte)
    (wire : ExactBytes n) (h : parseExact n bytes = some wire) :
    serializeExact wire = bytes := by
  simp only [parseExact] at h
  split at h
  · cases h
    rfl
  · contradiction

abbrev RuntimeExactWire (shape : RuntimeShape) :=
  ExactBytes (runtimeRepairedProofBytes shape)

def serializeRuntimeExact (shape : RuntimeShape)
    (wire : RuntimeExactWire shape) : List Byte := serializeExact wire

def parseRuntimeExact (shape : RuntimeShape)
    (bytes : List Byte) : Option (RuntimeExactWire shape) :=
  parseExact (runtimeRepairedProofBytes shape) bytes

theorem runtime_parse_serialize_roundtrip (shape : RuntimeShape)
    (wire : RuntimeExactWire shape) :
    parseRuntimeExact shape (serializeRuntimeExact shape wire) = some wire := by
  exact parse_serialize_roundtrip wire

theorem former_layout_is_rejected_by_runtime_exact_parser (shape : RuntimeShape) :
    parseRuntimeExact shape
      (List.replicate (runtimeFormerProofBytes shape) (0 : Byte)) = none := by
  unfold parseRuntimeExact parseExact
  split
  · rename_i h
    simp only [List.length_replicate] at h
    simp only [runtimeFormerProofBytes, runtimeRepairedProofBytes,
      formerFixedBytes] at h
    rw [retired_production_c1_span_is_8064] at h
    omega
  · rfl

theorem one_byte_truncation_is_rejected_for_every_runtime_shape
    (shape : RuntimeShape) :
    parseRuntimeExact shape
      (List.replicate (runtimeRepairedProofBytes shape - 1) (0 : Byte)) = none := by
  unfold parseRuntimeExact parseExact
  split
  · rename_i h
    simp only [List.length_replicate] at h
    simp [runtimeRepairedProofBytes, repairedFixedBytes] at h
  · rfl

theorem one_byte_append_is_rejected_for_every_runtime_shape
    (shape : RuntimeShape) :
    parseRuntimeExact shape
      (List.replicate (runtimeRepairedProofBytes shape + 1) (0 : Byte)) = none := by
  unfold parseRuntimeExact parseExact
  split
  · rename_i h
    simp only [List.length_replicate] at h
    omega
  · rfl

#print axioms retired_production_c1_span_is_8064
#print axioms repaired_offsets_are_contiguous
#print axioms fixed_span_total
#print axioms fixed_span_pairwise_disjoint
#print axioms fixed_span_unique
#print axioms every_fixed_byte_has_exactly_one_parser_span
#print axioms runtime_section_bytes_positive
#print axioms runtime_suffix_offsets_are_cumulative
#print axioms runtime_suffix_section_total
#print axioms runtime_suffix_sections_pairwise_disjoint
#print axioms runtime_suffix_section_unique
#print axioms every_runtime_suffix_byte_has_exactly_one_section
#print axioms fixed_span_stop_le_repairedFixedBytes
#print axioms runtime_span_total
#print axioms runtime_spans_pairwise_disjoint
#print axioms runtime_span_unique
#print axioms every_runtime_body_byte_has_exactly_one_span
#print axioms zeroToSeventeenQ18_injective
#print axioms zeroToSeventeen_shifted_record_counts
#print axioms zeroToSeventeen_shape_counts
#print axioms zeroToSeventeen_section_bytes
#print axioms zeroToSeventeen_runtime_suffix_is_13246
#print axioms zeroToSeventeen_runtime_body_is_32382
#print axioms current_fixture_section_sizes_are_exact
#print axioms current_fixture_runtime_suffix_is_56222
#print axioms current_fixture_repaired_proof_is_75358
#print axioms former_fixture_proof_is_83422
#print axioms runtime_repair_removes_exactly_8064_bytes
#print axioms runtime_repair_signed_delta_is_negative_8064
#print axioms parse_serialize_roundtrip
#print axioms rust_roundtrip_of_named_correspondence
#print axioms successful_parse_serializes_identically
#print axioms runtime_parse_serialize_roundtrip
#print axioms former_layout_is_rejected_by_runtime_exact_parser
#print axioms one_byte_truncation_is_rejected_for_every_runtime_shape
#print axioms one_byte_append_is_rejected_for_every_runtime_shape

end AspisFormal.V5ExactRuntimeWireRepair
