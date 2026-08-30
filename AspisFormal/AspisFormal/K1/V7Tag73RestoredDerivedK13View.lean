import AspisFormal.K1.V7Tag73RestoredNodeK13Classifier
import AspisFormal.K1.V7Tag73CanonicalOneFoldSchedule
import AspisFormal.K1.V7Tag73FixedFieldMessageBridge
import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.K1.V7Tag73Q16LedgerCertificate

/-!
# Verifier-derived K1.3 view for restored Tag-73 nodes

An adversarial restored child may put arbitrary values in the opaque parsed
`gamma`, `schedule`, and `queries` fields returned by the black-box prover.
Those fields therefore cannot be the knowledge-soundness input.  The live
future-free verifier derives gamma, alpha zero, and the selected q16 schedule
from its own random-oracle execution.

This module defines the corrected restored-node view.  Only the Merkle
openings and the 641 canonical fixed-field encodings remain prover/parser
owned.  The q16 query vector is definitionally the positions of an actually
executed `.q16Selected` transition.  Thus the K1.3 query event no longer needs
an equality premise relating an adversarial opaque field to verifier state.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RestoredDerivedK13View

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73Q16LedgerCertificate
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction
open AspisV6AcceptedPathObligations

noncomputable section

/-- Exact verifier-owned K1.3 data for one restored execution.  The first
fields canonically decode prover bytes.  Gamma and alpha zero are tied to
literal verifier records, while q16 selection is tied to the complete
first-cap-203 ledger retained by the final snapshot. -/
structure RestoredOperationalK13Data
    {Statement Payload : Type*}
    (environment : FutureFreeEnvironment)
    (node : RestoredK13Node Statement Payload) where
  decoded : Fin 641 → QM31Exact
  fixedDecode : FixedFieldDecodeExact node.adversaryValue.rawMessages decoded
  gamma : QM31Exact
  gammaBytes : Qm31Bytes
  gammaRecorded :
    { id := ChallengeId.gamma, value := gammaBytes } ∈
      node.verifierFinalState.current.decodedChallenges
  gammaDecoded : decodeTagQM31ExactLE gammaBytes = some gamma
  alphaZero : QM31Exact
  alphaZeroBytes : Qm31Bytes
  alphaZeroRecorded :
    { id := ChallengeId.alpha 0, value := alphaZeroBytes } ∈
      node.verifierFinalState.current.decodedChallenges
  alphaZeroDecoded : decodeTagQM31ExactLE alphaZeroBytes = some alphaZero
  priorCandidates : List DecodedQ16Candidate
  selectedCounter : Fin 64
  selectedSchedule : AspisK1.V7Tag73TranscriptSchedule.QuerySchedule
  priorHistory : Q16PriorNoncompactHistory environment selectedCounter
    priorCandidates
  selectedCompact : environment.frontierNodes selectedSchedule ≤ 203
  candidateLedgerExact :
    node.verifierFinalState.current.q16Candidates =
      priorCandidates ++
        [decodedScheduleRecord selectedCounter selectedSchedule]

/-- Repackage the data's q16 fields as the intrinsic selected-ledger
certificate for its immutable terminal snapshot. -/
def RestoredOperationalK13Data.selectedLedgerCertificate
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    {node : RestoredK13Node Statement Payload}
    (data : RestoredOperationalK13Data environment node) :
    SelectedQ16LedgerCertificate environment
      node.verifierFinalState.current where
  priorCandidates := data.priorCandidates
  selectedCounter := data.selectedCounter
  selectedSchedule := data.selectedSchedule
  priorHistory := data.priorHistory
  selectedCompact := data.selectedCompact
  ledgerExact := data.candidateLedgerExact

/-- Canonical fixed-field decoding is functional.  Thus the disclosed-final
message does not depend on which existential decoder witness was selected. -/
theorem restored_operational_k13_data_decoded_unique
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    {node : RestoredK13Node Statement Payload}
    (left right : RestoredOperationalK13Data environment node) :
    left.decoded = right.decoded := by
  funext index
  exact Option.some.inj ((left.fixedDecode index).symm.trans
    (right.fixedDecode index))

/-- The selected counter and schedule are fixed by the snapshot ledger, not
by the classical certificate choice used by the source provider. -/
theorem restored_operational_k13_data_selected_unique
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    {node : RestoredK13Node Statement Payload}
    (left right : RestoredOperationalK13Data environment node) :
    left.selectedCounter = right.selectedCounter ∧
      left.selectedSchedule = right.selectedSchedule := by
  exact selected_q16_ledger_certificate_selected_unique
    left.selectedLedgerCertificate right.selectedLedgerCertificate

/-- The corrected proof view: parser-owned openings, canonically decoded
fixed fields, and verifier-owned challenge/query data. -/
def restoredOperationalK13View
    {Statement Payload : Type*}
    {node : RestoredK13Node Statement Payload}
    {environment : FutureFreeEnvironment}
    (data : RestoredOperationalK13Data environment node) : Tag73K12ParsedProof :=
  { openings := (restoredNodeK12Proof node).openings
    gamma := data.gamma
    disclosedFinal := decodedFinalMessage data.decoded
    schedule := canonicalOneFoldSchedule data.alphaZero
    queries := data.selectedSchedule.positions }

@[simp] theorem restored_operational_view_openings
    {Statement Payload : Type*}
    {node : RestoredK13Node Statement Payload}
    {environment : FutureFreeEnvironment}
    (data : RestoredOperationalK13Data environment node) :
    (restoredOperationalK13View data).openings =
      (restoredNodeK12Proof node).openings := by
  rfl

@[simp] theorem restored_operational_view_gamma
    {Statement Payload : Type*}
    {node : RestoredK13Node Statement Payload}
    {environment : FutureFreeEnvironment}
    (data : RestoredOperationalK13Data environment node) :
    (restoredOperationalK13View data).gamma = data.gamma := by
  rfl

@[simp] theorem restored_operational_view_alpha_zero
    {Statement Payload : Type*}
    {node : RestoredK13Node Statement Payload}
    {environment : FutureFreeEnvironment}
    (data : RestoredOperationalK13Data environment node) :
    (restoredOperationalK13View data).schedule.alpha = data.alphaZero := by
  rfl

@[simp] theorem restored_operational_view_queries
    {Statement Payload : Type*}
    {node : RestoredK13Node Statement Payload}
    {environment : FutureFreeEnvironment}
    (data : RestoredOperationalK13Data environment node) :
    (restoredOperationalK13View data).queries =
      data.selectedSchedule.positions := by
  rfl

@[simp] theorem restored_operational_view_final_coefficient
    {Statement Payload : Type*}
    {node : RestoredK13Node Statement Payload}
    {environment : FutureFreeEnvironment}
    (data : RestoredOperationalK13Data environment node)
    (coefficient : Fin 256) :
    (restoredOperationalK13View data).disclosedFinal coefficient =
      (decodedFixedFieldView data.decoded).finalCoefficient coefficient := by
  rfl

/-- K1.2 authentication is unchanged; only the downstream algebraic view is
repaired to use verifier-derived data. -/
structure RestoredOperationalK13Certificate
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload)
    (data : RestoredOperationalK13Data environment node) where
  k12 : RestoredNodeK12Certificate node
  k13 : ParsedK13Certificate decoder k12.words
    (restoredOperationalK13View data)

inductive RestoredOperationalK13Error
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload)
    (data : RestoredOperationalK13Data environment node) : Type
  | k12 (error : RestoredNodeK12Error node)
  | k13 (words : ExtractedWords)
      (error : ParsedK13Error decoder words
        (restoredOperationalK13View data))

/-- Proposition-level inventory for the corrected restored-node classifier.
Every disjunct is an existing K1.2 or K1.3 mathematical failure evaluated on
the verifier-derived view; no opaque classifier-result event is introduced. -/
def RestoredOperationalK13FailureEvent
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload)
    (data : RestoredOperationalK13Data environment node) : Prop :=
  (¬ accepted_two_tree_openings (restoredNodeK12Truncate node)
      (restoredNodeK12Roots node) (restoredNodeK12Openings node)) ∨
  V7MerkleExtractionFailure (restoredNodeK12Truncate node)
      (restoredNodeK12Roots node) (restoredNodeK12Openings node)
      (restoredNodeK12OrderedQueries node) ∨
  ∃ words : ExtractedWords,
    (¬ IdealAccepts (restoredOperationalK13View data).schedule
      (decoderCodeEncoders decoder)
      (parsedK13Transcript words (restoredOperationalK13View data))
      (restoredOperationalK13View data).queries) ∨
    QueryPhaseFailure (restoredOperationalK13View data).schedule
      (decoderCodeEncoders decoder)
      (parsedK13Transcript words (restoredOperationalK13View data))
      (restoredOperationalK13View data).queries ∨
    OneFoldReductionFailure (restoredOperationalK13View data).schedule
      (decoderCodeEncoders decoder)
      (parsedK13Transcript words (restoredOperationalK13View data)) ∨
    InitialListCapFailure (decoderCodeEncoders decoder)
      (parsedK13Transcript words (restoredOperationalK13View data))

/-- A returned corrected classifier error always inhabits exactly one of the
explicit mathematical failure families above. -/
theorem restored_operational_k13_error_implies_failure_event
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {node : RestoredK13Node Statement Payload}
    {data : RestoredOperationalK13Data environment node}
    (error : RestoredOperationalK13Error decoder node data) :
    RestoredOperationalK13FailureEvent decoder node data := by
  cases error with
  | k12 error =>
      cases error with
      | openingAuthenticationRejected rejected => exact .inl rejected
      | extractionFailure reason failed => exact .inr (.inl ⟨reason, failed⟩)
  | k13 words error =>
      refine .inr (.inr ⟨words, ?_⟩)
      cases error with
      | idealRejected rejected => exact .inl rejected
      | queryPhaseFailure failure => exact .inr (.inl failure)
      | oneFoldReductionFailure failure => exact .inr (.inr (.inl failure))
      | initialListCapFailure failure => exact .inr (.inr (.inr failure))

/-- Total restored-node K1.3 classifier over the corrected operational view. -/
noncomputable def classifyRestoredOperationalK13
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload)
    (data : RestoredOperationalK13Data environment node) :
    RestoredOperationalK13Certificate decoder node data ⊕
      RestoredOperationalK13Error decoder node data :=
  match classifyRestoredNodeK12 node with
  | .inr error => .inr (.k12 error)
  | .inl k12 =>
      match classifyParsedK13 decoder k12.words
          (restoredOperationalK13View data) with
      | .inl k13 => .inl ⟨k12, k13⟩
      | .inr error => .inr (.k13 k12.words error)

/-- A q16 failure for the corrected view is attached to the selected record
of the exact retained first-cap-203 ledger, with no parsed-query equality
premise. -/
theorem restored_operational_query_failure_selected_all_in_bad
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {node : RestoredK13Node Statement Payload}
    (data : RestoredOperationalK13Data environment node)
    (k12 : RestoredNodeK12Certificate node)
    (failure : QueryPhaseFailure
      (restoredOperationalK13View data).schedule
      (decoderCodeEncoders decoder)
      (parsedK13Transcript k12.words (restoredOperationalK13View data))
      (restoredOperationalK13View data).queries) :
    ∃ bad : Finset (Fin 262144),
      bad.card ≤ 9557 ∧
      node.verifierFinalState.current.q16Candidates =
        data.priorCandidates ++
          [decodedScheduleRecord data.selectedCounter
            data.selectedSchedule] ∧
      decodedScheduleRecord data.selectedCounter data.selectedSchedule ∈
        node.verifierFinalState.current.q16Candidates ∧
      AllInBad bad data.selectedSchedule.positions := by
  let bad := consistencySet (restoredOperationalK13View data).schedule
    (decoderCodeEncoders decoder)
    (parsedK13Transcript k12.words (restoredOperationalK13View data))
  refine ⟨bad, failure.2, data.candidateLedgerExact, ?_, ?_⟩
  · rw [data.candidateLedgerExact]
    simp
  intro ordinal
  have member := accepted_queries_mem_consistencySet
    (restoredOperationalK13View data).schedule
    (decoderCodeEncoders decoder)
    (parsedK13Transcript k12.words (restoredOperationalK13View data))
    (restoredOperationalK13View data).queries failure.1 ordinal
  simpa [bad, restoredOperationalK13View] using member

/-! ## Restoration-wide corrected q16 event -/

/-- The exact q16 failure event over a completed restoration accumulator,
using only verifier-derived challenge/query data.  Requiring the retained
node to be `.done` excludes normally returned verifier rejections. -/
def RestoredOperationalK13QueryEvent
    {Statement Payload : Type*}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (environment : FutureFreeEnvironment)
    (accumulator : ConcreteRestorationAccumulator Statement
      Tag73K12ParsedProof Payload) : Prop :=
  ∃ (node : RestoredK13Node Statement Payload),
    node ∈ accumulator.nodes ∧
    node.verifierFinalState.current.control = .done ∧
    ∃ (data : RestoredOperationalK13Data environment node)
      (k12 : RestoredNodeK12Certificate node),
      QueryPhaseFailure (restoredOperationalK13View data).schedule
        (decoderCodeEncoders decoder)
        (parsedK13Transcript k12.words (restoredOperationalK13View data))
        (restoredOperationalK13View data).queries

/-- Membership in the corrected restoration-wide event exposes the exact
accepted stored node and its retained selected q16 record, whose sixteen
positions all lie in one set of size at most 9557. -/
theorem restored_operational_query_event_exposes_selected_bad_set
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {accumulator : ConcreteRestorationAccumulator Statement
      Tag73K12ParsedProof Payload}
    (event : RestoredOperationalK13QueryEvent decoder environment accumulator) :
    ∃ (node : RestoredK13Node Statement Payload)
        (data : RestoredOperationalK13Data environment node)
        (bad : Finset (Fin 262144)),
      node ∈ accumulator.nodes ∧
      node.verifierFinalState.current.control = .done ∧
      bad.card ≤ 9557 ∧
      node.verifierFinalState.current.q16Candidates =
        data.priorCandidates ++
          [decodedScheduleRecord data.selectedCounter
            data.selectedSchedule] ∧
      decodedScheduleRecord data.selectedCounter data.selectedSchedule ∈
        node.verifierFinalState.current.q16Candidates ∧
      AllInBad bad data.selectedSchedule.positions := by
  rcases event with ⟨node, member, done, data, k12, failure⟩
  obtain ⟨bad, badCard, ledgerExact, selectedMember, allBad⟩ :=
    restored_operational_query_failure_selected_all_in_bad data k12 failure
  exact ⟨node, data, bad, member, done, badCard, ledgerExact,
    selectedMember, allBad⟩

#print axioms restored_operational_view_queries
#print axioms restored_operational_k13_data_decoded_unique
#print axioms restored_operational_k13_data_selected_unique
#print axioms classifyRestoredOperationalK13
#print axioms restored_operational_k13_error_implies_failure_event
#print axioms restored_operational_query_failure_selected_all_in_bad
#print axioms restored_operational_query_event_exposes_selected_bad_set

end

end AspisK1.V7Tag73RestoredDerivedK13View
