import AspisFormal.K1.V7Tag73FutureFreeFullControl

/-!
# Exact q16 ledger certificate

This low-level module records the restoration-stable first-compact q16
certificate created by the executable candidate controller.  It is kept
below the checked-path and restoration layers so both can consume the same
proof-relevant object without a dependency cycle.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73Q16LedgerCertificate

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl

noncomputable section

structure SelectedQ16LedgerCertificate
    (environment : FutureFreeEnvironment)
    (snapshot : FutureFreeSnapshot) : Type where
  priorCandidates : List DecodedQ16Candidate
  selectedCounter : Fin 64
  selectedSchedule : QuerySchedule
  priorHistory : Q16PriorNoncompactHistory environment selectedCounter
    priorCandidates
  selectedCompact : environment.frontierNodes selectedSchedule ≤ 203
  ledgerExact : snapshot.q16Candidates =
    priorCandidates ++
      [decodedScheduleRecord selectedCounter selectedSchedule]

theorem selected_q16_ledger_contains_selected
    {environment : FutureFreeEnvironment}
    {snapshot : FutureFreeSnapshot}
    (certificate : SelectedQ16LedgerCertificate environment snapshot) :
    decodedScheduleRecord certificate.selectedCounter
        certificate.selectedSchedule ∈ snapshot.q16Candidates := by
  rw [certificate.ledgerExact]
  simp

theorem selected_q16_ledger_prior_records_are_noncompact
    {environment : FutureFreeEnvironment}
    {snapshot : FutureFreeSnapshot}
    (certificate : SelectedQ16LedgerCertificate environment snapshot) :
    ∀ record ∈ certificate.priorCandidates,
      record.counter.val < certificate.selectedCounter.val ∧
      ∃ schedule,
        record = decodedScheduleRecord record.counter schedule ∧
        203 < environment.frontierNodes schedule := by
  exact q16_prior_noncompact_history_contains_only_earlier_noncompact
    environment certificate.selectedCounter certificate.priorCandidates
      certificate.priorHistory

/-- Two certificates for the same immutable snapshot cannot select different
q16 records.  Both exact ledgers end in their selected record, so equality of
the snapshot ledger fixes the counter and schedule independently of any
classical choice used to obtain a certificate. -/
theorem selected_q16_ledger_certificate_selected_unique
    {environment : FutureFreeEnvironment}
    {snapshot : FutureFreeSnapshot}
    (left right : SelectedQ16LedgerCertificate environment snapshot) :
    left.selectedCounter = right.selectedCounter ∧
      left.selectedSchedule = right.selectedSchedule := by
  have ledgers :
      left.priorCandidates ++
          [decodedScheduleRecord left.selectedCounter left.selectedSchedule] =
        right.priorCandidates ++
          [decodedScheduleRecord right.selectedCounter
            right.selectedSchedule] :=
    left.ledgerExact.symm.trans right.ledgerExact
  have lastRecords := congrArg List.getLast? ledgers
  have recordExact :
      decodedScheduleRecord left.selectedCounter left.selectedSchedule =
        decodedScheduleRecord right.selectedCounter right.selectedSchedule := by
    simpa using lastRecords
  have counterExact := congrArg DecodedQ16Candidate.counter recordExact
  have outcomeExact := congrArg DecodedQ16Candidate.outcome recordExact
  constructor
  · simpa [decodedScheduleRecord] using counterExact
  · exact CandidateOutcome.schedule.inj
      (by simpa [decodedScheduleRecord] using outcomeExact)

def SelectedQ16LedgerCertificate.transport
    {environment : FutureFreeEnvironment}
    {before after : FutureFreeSnapshot}
    (certificate : SelectedQ16LedgerCertificate environment before)
    (ledgerPreserved : after.q16Candidates = before.q16Candidates) :
    SelectedQ16LedgerCertificate environment after :=
  { priorCandidates := certificate.priorCandidates
    selectedCounter := certificate.selectedCounter
    selectedSchedule := certificate.selectedSchedule
    priorHistory := certificate.priorHistory
    selectedCompact := certificate.selectedCompact
    ledgerExact := ledgerPreserved.trans certificate.ledgerExact }

def compact_candidate_constructs_selected_q16_ledger
    (environment : FutureFreeEnvironment)
    (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) (schedule : QuerySchedule)
    (history : Q16PriorNoncompactHistory environment counter
      snapshot.q16Candidates)
    (decoded : environment.decoders.candidate counter
      (outputs ++ [output]) = some (.schedule schedule))
    (compact : environment.frontierNodes schedule ≤ 203) :
    SelectedQ16LedgerCertificate environment
      (processFutureFreeCandidateBlock environment snapshot base counter
        outputs remaining output nextCore) := by
  have exact := compact_candidate_block_forces_selection environment snapshot
    base counter outputs remaining output nextCore schedule decoded compact
  exact
    { priorCandidates := snapshot.q16Candidates
      selectedCounter := counter
      selectedSchedule := schedule
      priorHistory := history
      selectedCompact := compact
      ledgerExact := by rw [exact] }

#print axioms selected_q16_ledger_contains_selected
#print axioms selected_q16_ledger_prior_records_are_noncompact
#print axioms selected_q16_ledger_certificate_selected_unique
#print axioms SelectedQ16LedgerCertificate.transport
#print axioms compact_candidate_constructs_selected_q16_ledger

end

end AspisK1.V7Tag73Q16LedgerCertificate
