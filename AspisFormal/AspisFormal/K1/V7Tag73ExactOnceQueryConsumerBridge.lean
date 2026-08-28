import Mathlib

/-!
# Exact-once canonical query-consumer bridge for selected Tag-73

This module freezes the byte and limb accounting of the selected
`V7CanonicalOneFoldWire::parse_deferred_query_canonicality` path at source
revision `8178d3de1d24d7a3a0102739cb63aca8d7a125a8`.

The deferred parser does not weaken canonicality.  Its accepted-path query
callback visits the sixteen authenticated records in a permutation of their
wire ordinals.  For every record it passes the exact 403-byte C1 slice and
186-byte C2 slice to `gamma_combine_v6_packed_layer0`.  That routine invokes
the checked aligned decoder at widths 104 and 48.  Thus a successful callback
checks the finite set `Fin 16 × (Fin 104 ⊕ Fin 48)`, whose cardinality is
2,432, exactly once.  The 2,564 fixed-section limbs remain checked by the
canonical fixed reader.

The Charon/Aeneas bundle in
`aeneas-verif/v7-tag73-exact-once-query-source-20260828` pins those source
calls and their result flow.  This file supplies the assumption-free finite
accounting, fail-closed layout/canonicality statements, and the accepted-path
transcript-order equivalence consumed by that source bridge.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactOnceQueryConsumerBridge

/-! ## Source-frozen dimensions -/

def selectedRustRevision : String :=
  "8178d3de1d24d7a3a0102739cb63aca8d7a125a8"

def queryCount : Nat := 16
def c1LimbsPerQuery : Nat := 104
def c2LimbsPerQuery : Nat := 48
def limbsPerQuery : Nat := c1LimbsPerQuery + c2LimbsPerQuery
def fixedSectionLimbs : Nat := 2564
def querySectionLimbs : Nat := queryCount * limbsPerQuery
def totalCanonicalLimbs : Nat := fixedSectionLimbs + querySectionLimbs

def c1PackedBytesPerQuery : Nat := c1LimbsPerQuery * 31 / 8
def c2PackedBytesPerQuery : Nat := c2LimbsPerQuery * 31 / 8
def privateSaltBytes : Nat := 32
def queryRecordBytes : Nat :=
  c1PackedBytesPerQuery + c2PackedBytesPerQuery + privateSaltBytes
def querySectionBytes : Nat := queryCount * queryRecordBytes

def canonicalFixedBytes : Nat := 10256
def compactDigestBytes : Nat := 26
def workNonceBytes : Nat := 24
def canonicalBodyWithoutFrontiers : Nat :=
  canonicalFixedBytes + 2 * compactDigestBytes + workNonceBytes +
    querySectionBytes
def frontierCapPerTree : Nat := 209
def canonicalBodyBytes (frontierNodes : Nat) : Nat :=
  canonicalBodyWithoutFrontiers + 2 * frontierNodes * compactDigestBytes

theorem selected_revision_is_pinned :
    selectedRustRevision =
      "8178d3de1d24d7a3a0102739cb63aca8d7a125a8" := by
  rfl

theorem exact_selected_dimensions :
    limbsPerQuery = 152 ∧
      querySectionLimbs = 2432 ∧
      fixedSectionLimbs = 2564 ∧
      totalCanonicalLimbs = 4996 ∧
      c1PackedBytesPerQuery = 403 ∧
      c2PackedBytesPerQuery = 186 ∧
      queryRecordBytes = 621 ∧
      querySectionBytes = 9936 ∧
      canonicalBodyWithoutFrontiers = 20268 := by
  norm_num [limbsPerQuery, querySectionLimbs, fixedSectionLimbs,
    totalCanonicalLimbs, c1PackedBytesPerQuery, c2PackedBytesPerQuery,
    c1LimbsPerQuery, c2LimbsPerQuery, queryCount, privateSaltBytes,
    queryRecordBytes, querySectionBytes, canonicalFixedBytes,
    compactDigestBytes, workNonceBytes, canonicalBodyWithoutFrontiers]

/-! ## Exact finite coverage -/

abbrev QueryOrdinal := Fin 16
abbrev C1Limb := Fin 104
abbrev C2Limb := Fin 48
abbrev QueryLimb := QueryOrdinal × (C1Limb ⊕ C2Limb)

/-- The selected source constructs `(query, ordinal)` for all sixteen array
positions, sorts those records, and consumes the sorted owned array.  Sorting
changes order but not this ordinal schedule. -/
def canonicalOrdinalSchedule : List QueryOrdinal := List.ofFn id

/-- Every limb in a query record is visited when, and only when, its query
ordinal is consumed.  This count therefore captures multiplicity rather than
only finite-set coverage. -/
def queryLimbVisitCount (schedule : List QueryOrdinal) (limb : QueryLimb) : Nat :=
  schedule.count limb.1

theorem canonical_ordinal_schedule_has_sixteen_entries :
    canonicalOrdinalSchedule.length = 16 := by
  simp [canonicalOrdinalSchedule]

theorem canonical_ordinal_schedule_visits_each_limb_exactly_once
    (limb : QueryLimb) :
    queryLimbVisitCount canonicalOrdinalSchedule limb = 1 := by
  rcases limb with ⟨ordinal, payload⟩
  fin_cases ordinal <;> rfl

/-- The finite set checked for one query ordinal.  A `Finset` is deliberate:
membership has no multiplicity, matching the source obligation that the
schedule contains every ordinal once. -/
def recordCheckedSet (ordinal : QueryOrdinal) : Finset QueryLimb :=
  Finset.univ.filter fun limb => limb.1 = ordinal

/-- The set checked by a source loop whose sorted ordinal array is represented
by `schedule`. -/
def consumerCheckedSet (schedule : Finset QueryOrdinal) : Finset QueryLimb :=
  schedule.biUnion recordCheckedSet

theorem query_limb_fintype_card : Fintype.card QueryLimb = 2432 := by
  norm_num

theorem record_checked_set_card (ordinal : QueryOrdinal) :
    (recordCheckedSet ordinal).card = 152 := by
  classical
  have exactProduct : recordCheckedSet ordinal =
      ({ordinal} : Finset QueryOrdinal) ×ˢ (Finset.univ : Finset (C1Limb ⊕ C2Limb)) := by
    ext limb
    rcases limb with ⟨query, limb⟩
    simp only [recordCheckedSet, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_product, Finset.mem_singleton]
    constructor
    · intro equal
      subst query
      exact ⟨rfl, True.intro⟩
    · intro member
      exact member.1
  rw [exactProduct, Finset.card_product]
  norm_num

theorem all_ordinals_check_every_query_limb :
    consumerCheckedSet Finset.univ = Finset.univ := by
  classical
  ext limb
  simp [consumerCheckedSet, recordCheckedSet]

theorem exact_once_query_coverage :
    (consumerCheckedSet Finset.univ).card = 2432 := by
  rw [all_ordinals_check_every_query_limb]
  exact query_limb_fintype_card

theorem fixed_and_query_checks_partition_all_4996_limbs :
    fixedSectionLimbs + (consumerCheckedSet Finset.univ).card = 4996 := by
  rw [exact_once_query_coverage]
  rfl

/-! ## Fail-closed layout and canonicality -/

inductive DeferredQueryError where
  | frontierTooLarge
  | wrongLength
  | nonCanonicalM31
  | invalidQuerySchedule
  deriving DecidableEq, Repr

def deferredLayoutCheck (frontierNodes actualBytes : Nat) :
    Except DeferredQueryError Unit :=
  if frontierNodes > frontierCapPerTree then
    .error .frontierTooLarge
  else if actualBytes ≠ canonicalBodyBytes frontierNodes then
    .error .wrongLength
  else
    .ok ()

theorem deferred_layout_accepts_iff_exact
    (frontierNodes actualBytes : Nat) :
    deferredLayoutCheck frontierNodes actualBytes = .ok () ↔
      frontierNodes ≤ frontierCapPerTree ∧
        actualBytes = canonicalBodyBytes frontierNodes := by
  unfold deferredLayoutCheck
  by_cases oversized : frontierNodes > frontierCapPerTree
  · simp [oversized, Nat.not_le_of_gt oversized]
  · have withinCap : frontierNodes ≤ frontierCapPerTree :=
      Nat.le_of_not_gt oversized
    simp [oversized, withinCap]

theorem deferred_layout_rejects_truncation
    {frontierNodes actualBytes : Nat}
    (withinCap : frontierNodes ≤ frontierCapPerTree)
    (truncated : actualBytes < canonicalBodyBytes frontierNodes) :
    deferredLayoutCheck frontierNodes actualBytes = .error .wrongLength := by
  simp [deferredLayoutCheck, Nat.not_lt.mpr withinCap,
    ne_of_lt truncated]

theorem deferred_layout_rejects_trailing_bytes
    {frontierNodes actualBytes : Nat}
    (withinCap : frontierNodes ≤ frontierCapPerTree)
    (trailing : canonicalBodyBytes frontierNodes < actualBytes) :
    deferredLayoutCheck frontierNodes actualBytes = .error .wrongLength := by
  simp [deferredLayoutCheck, Nat.not_lt.mpr withinCap,
    ne_of_gt trailing]

theorem deferred_layout_rejects_oversized_frontier
    {frontierNodes actualBytes : Nat}
    (oversized : frontierCapPerTree < frontierNodes) :
    deferredLayoutCheck frontierNodes actualBytes =
      .error .frontierTooLarge := by
  simp [deferredLayoutCheck, oversized]

/-- The packed decoder accepts exactly M31 representatives strictly below
`2^31 - 1`; the all-ones 31-bit word is rejected. -/
def CanonicalM31 (value : Fin (2 ^ 31)) : Prop :=
  value.val < 2 ^ 31 - 1

def queryCanonical (values : QueryLimb → Fin (2 ^ 31)) : Prop :=
  ∀ limb, CanonicalM31 (values limb)

noncomputable def queryCanonicalBool
    (values : QueryLimb → Fin (2 ^ 31)) : Bool := by
  classical
  exact decide (
    (∀ query : QueryOrdinal, ∀ limb : C1Limb,
      CanonicalM31 (values (query, Sum.inl limb))) ∧
    (∀ query : QueryOrdinal, ∀ limb : C2Limb,
      CanonicalM31 (values (query, Sum.inr limb))))

noncomputable def deferredConsumerCheck (values : QueryLimb → Fin (2 ^ 31)) :
    Except DeferredQueryError Unit :=
  if queryCanonicalBool values then .ok () else .error .nonCanonicalM31

theorem queryCanonicalBool_eq_true_iff
    (values : QueryLimb → Fin (2 ^ 31)) :
    queryCanonicalBool values = true ↔ queryCanonical values := by
  simp only [queryCanonicalBool, decide_eq_true_eq]
  constructor
  · intro canonical limb
    rcases limb with ⟨query, limb⟩
    cases limb with
    | inl c1 => exact canonical.1 query c1
    | inr c2 => exact canonical.2 query c2
  · intro canonical
    constructor
    · intro query limb
      exact canonical (query, Sum.inl limb)
    · intro query limb
      exact canonical (query, Sum.inr limb)

theorem deferred_consumer_accepts_iff_every_limb_canonical
    (values : QueryLimb → Fin (2 ^ 31)) :
    deferredConsumerCheck values = .ok () ↔ queryCanonical values := by
  rw [← queryCanonicalBool_eq_true_iff]
  simp [deferredConsumerCheck]

theorem deferred_consumer_rejects_any_malformed_limb
    (values : QueryLimb → Fin (2 ^ 31)) (malformed : QueryLimb)
    (invalid : ¬ CanonicalM31 (values malformed)) :
    deferredConsumerCheck values = .error .nonCanonicalM31 := by
  have notCanonical : ¬ queryCanonical values := by
    intro allCanonical
    exact invalid (allCanonical malformed)
  have checkFalse : queryCanonicalBool values = false := by
    apply Bool.eq_false_iff.mpr
    intro checkTrue
    exact notCanonical ((queryCanonicalBool_eq_true_iff values).mp checkTrue)
  simp [deferredConsumerCheck, checkFalse]

/-! ## Transcript-order preservation -/

/-- Only transcript-mutating operations appear in this trace.  Structural
layout scans and packed canonicality checks deliberately emit no event. -/
inductive TranscriptEvent where
  | absorb (label : Nat)
  | squeeze (label : Nat)
  deriving DecidableEq, Repr

structure RunObservation where
  accepted : Bool
  transcript : List TranscriptEvent
  deriving DecidableEq, Repr

/-- Eager validation rejects malformed query limbs before entering the
transcript, as the standalone source parser does. -/
def eagerObservation (canonical : Bool) (trace : List TranscriptEvent) :
    RunObservation :=
  if canonical then ⟨true, trace⟩ else ⟨false, []⟩

/-- Deferred validation performs the same transcript operations and rejects
at the sole query consumer before acceptance. -/
def deferredObservation (canonical : Bool) (trace : List TranscriptEvent) :
    RunObservation :=
  ⟨canonical, trace⟩

theorem accepted_deferred_path_preserves_transcript_order
    (trace : List TranscriptEvent) :
    eagerObservation true trace = deferredObservation true trace := by
  rfl

/-- Deferred canonicality validation neither absorbs nor squeezes: it leaves
the surrounding transcript trace byte-for-byte and order-for-order unchanged,
including executions that later reject at the query consumer. -/
theorem deferred_validation_never_changes_transcript
    (canonical : Bool) (trace : List TranscriptEvent) :
    (deferredObservation canonical trace).transcript = trace := by
  rfl

theorem malformed_eager_and_deferred_paths_both_reject
    (trace : List TranscriptEvent) :
    (eagerObservation false trace).accepted = false ∧
      (deferredObservation false trace).accepted = false := by
  constructor <;> rfl

/-- Capstone consumed by the source bridge: accepted deferred execution has
the same transcript order as eager execution, covers exactly all 2,432 query
limbs, and complements the 2,564 fixed limbs to 4,996. -/
theorem accepted_exact_once_query_consumer_capstone
    (trace : List TranscriptEvent) :
    eagerObservation true trace = deferredObservation true trace ∧
      (∀ limb : QueryLimb,
        queryLimbVisitCount canonicalOrdinalSchedule limb = 1) ∧
      (consumerCheckedSet Finset.univ).card = 2432 ∧
      fixedSectionLimbs + (consumerCheckedSet Finset.univ).card = 4996 := by
  exact ⟨accepted_deferred_path_preserves_transcript_order trace,
    canonical_ordinal_schedule_visits_each_limb_exactly_once,
    exact_once_query_coverage,
    fixed_and_query_checks_partition_all_4996_limbs⟩

#print axioms selected_revision_is_pinned
#print axioms exact_selected_dimensions
#print axioms record_checked_set_card
#print axioms all_ordinals_check_every_query_limb
#print axioms exact_once_query_coverage
#print axioms fixed_and_query_checks_partition_all_4996_limbs
#print axioms canonical_ordinal_schedule_has_sixteen_entries
#print axioms canonical_ordinal_schedule_visits_each_limb_exactly_once
#print axioms deferred_layout_accepts_iff_exact
#print axioms deferred_layout_rejects_truncation
#print axioms deferred_layout_rejects_trailing_bytes
#print axioms deferred_layout_rejects_oversized_frontier
#print axioms deferred_consumer_accepts_iff_every_limb_canonical
#print axioms deferred_consumer_rejects_any_malformed_limb
#print axioms accepted_deferred_path_preserves_transcript_order
#print axioms deferred_validation_never_changes_transcript
#print axioms malformed_eager_and_deferred_paths_both_reject
#print axioms accepted_exact_once_query_consumer_capstone

end AspisK1.V7Tag73ExactOnceQueryConsumerBridge
