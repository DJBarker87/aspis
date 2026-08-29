import AspisFormal.K1.V7Tag73Q16LedgerCertificate
import AspisFormal.K1.V7Tag73ConcreteRestorationClient

/-!
# Q16 ledger invariant for the executable future-free controller

Restoration may resume inside the q16 scan, so an accepted child cannot rely
on a root-only fixed-tape argument.  This module records the proof-relevant
ledger phase directly on a live controller snapshot:

* the adaptive prefix has an empty ledger;
* a q16 absorb/sample state carries the exact earlier-noncompact history;
* a restore with a successor carries that history at the successor counter;
* a selected or completed state carries the exact first-compact certificate;
* explicit rejection controls impose no success obligation.

The central theorem below proves the difficult decoder transition directly
from `processFutureFreeCandidateBlock`.  It does not assume acceptance,
uniformity, or any probability conclusion.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73Q16LedgerControlInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73Q16LedgerCertificate
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73ConcreteRestorationClient

noncomputable section

def remainingQ16MarkerCount : List FutureFreeSlot → Nat
  | [] => 0
  | .beginQ16 :: remaining => remainingQ16MarkerCount remaining + 1
  | _ :: remaining => remainingQ16MarkerCount remaining

/-- Ordinary linear/submission controls have exactly one future q16 marker
and an empty ledger before the scan, or no future marker and a retained
selected certificate after the scan.  This also rules out malformed duplicate
markers while making the phase transition algebraic. -/
def NormalQ16LedgerPhase (environment : FutureFreeEnvironment)
    (remaining : List FutureFreeSlot) (snapshot : FutureFreeSnapshot) : Prop :=
  (remainingQ16MarkerCount remaining = 1 ∧
      snapshot.q16Candidates = []) ∨
    (remainingQ16MarkerCount remaining = 0 ∧
      Nonempty (SelectedQ16LedgerCertificate environment snapshot))

/-- Proof-relevant ledger phase attached to each executable control. -/
def SnapshotQ16LedgerInvariant (environment : FutureFreeEnvironment)
    (snapshot : FutureFreeSnapshot) : Prop :=
  match snapshot.control with
  | .adaptive _ => snapshot.q16Candidates = []
  | .linear remaining => NormalQ16LedgerPhase environment remaining snapshot
  | .absorbPayload _ remaining =>
      NormalQ16LedgerPhase environment remaining snapshot
  | .workCheck _ _ remaining =>
      NormalQ16LedgerPhase environment remaining snapshot
  | .workCheckpoint _ _ remaining =>
      NormalQ16LedgerPhase environment remaining snapshot
  | .workAbsorb _ _ remaining =>
      NormalQ16LedgerPhase environment remaining snapshot
  | .sampleChallenge _ _ remaining =>
      NormalQ16LedgerPhase environment remaining snapshot
  | .q16Absorb _ counter remaining =>
      remainingQ16MarkerCount remaining = 0 ∧
        Q16PriorNoncompactHistory environment counter snapshot.q16Candidates
  | .q16Sample _ counter _ remaining =>
      remainingQ16MarkerCount remaining = 0 ∧
        Q16PriorNoncompactHistory environment counter snapshot.q16Candidates
  | .q16Restore _ _ nextCounter remaining =>
      match nextCounter with
      | some next =>
          remainingQ16MarkerCount remaining = 0 ∧
            Q16PriorNoncompactHistory environment next snapshot.q16Candidates
      | none => True
  | .q16Selected _ _ _ remaining =>
      remainingQ16MarkerCount remaining = 0 ∧
        Nonempty (SelectedQ16LedgerCertificate environment snapshot)
  | .q16SamplerReject _ _ | .q16AllNoncompactReject | .rejected _ => True
  | .done => Nonempty (SelectedQ16LedgerCertificate environment snapshot)

@[simp] theorem initial_snapshot_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (bindings : FixedBindings) :
    SnapshotQ16LedgerInvariant environment
      (initialFutureFreeSnapshot bindings) := by
  rfl

/-- An exact selected certificate survives any control-only snapshot update
that leaves the candidate ledger unchanged. -/
def selected_certificate_of_ledger_preserved
    {environment : FutureFreeEnvironment}
    {before after : FutureFreeSnapshot}
    (certificate : SelectedQ16LedgerCertificate environment before)
    (ledgerPreserved : after.q16Candidates = before.q16Candidates) :
    SelectedQ16LedgerCertificate environment after :=
  certificate.transport ledgerPreserved

theorem normal_q16_ledger_phase_transport
    {environment : FutureFreeEnvironment}
    {remaining : List FutureFreeSlot}
    {before after : FutureFreeSnapshot}
    (ledgerPreserved : after.q16Candidates = before.q16Candidates)
    (invariant : NormalQ16LedgerPhase environment remaining before) :
    NormalQ16LedgerPhase environment remaining after := by
  rcases invariant with ⟨markerCount, empty⟩ | ⟨markerCount, ⟨certificate⟩⟩
  · exact Or.inl ⟨markerCount, ledgerPreserved.trans empty⟩
  · exact Or.inr ⟨markerCount, ⟨certificate.transport ledgerPreserved⟩⟩

/-- The phase predicate depends on control and the candidate ledger only.
This theorem transports its proof across account/binding/core updates that
leave those two fields exact. -/
theorem snapshot_q16_ledger_invariant_transport
    {environment : FutureFreeEnvironment}
    {before after : FutureFreeSnapshot}
    (controlPreserved : after.control = before.control)
    (ledgerPreserved : after.q16Candidates = before.q16Candidates)
    (invariant : SnapshotQ16LedgerInvariant environment before) :
    SnapshotQ16LedgerInvariant environment after := by
  rw [SnapshotQ16LedgerInvariant, controlPreserved]
  cases controlExact : before.control <;>
    rw [SnapshotQ16LedgerInvariant, controlExact] at invariant
  case adaptive => simpa [ledgerPreserved] using invariant
  case linear remaining =>
    exact normal_q16_ledger_phase_transport ledgerPreserved invariant
  case absorbPayload payload remaining =>
    exact normal_q16_ledger_phase_transport ledgerPreserved invariant
  case workCheck stage nonce remaining =>
    exact normal_q16_ledger_phase_transport ledgerPreserved invariant
  case workCheckpoint stage nonce remaining =>
    exact normal_q16_ledger_phase_transport ledgerPreserved invariant
  case workAbsorb stage nonce remaining =>
    exact normal_q16_ledger_phase_transport ledgerPreserved invariant
  case sampleChallenge id outputs remaining =>
    exact normal_q16_ledger_phase_transport ledgerPreserved invariant
  case q16Absorb base counter remaining =>
    simpa [ledgerPreserved] using invariant
  case q16Sample base counter outputs remaining =>
    simpa [ledgerPreserved] using invariant
  case q16Restore base counter nextCounter remaining =>
    cases nextCounter with
    | none => trivial
    | some next => simpa [ledgerPreserved] using invariant
  case q16Selected base counter schedule remaining =>
    rcases invariant with ⟨markerCount, ⟨certificate⟩⟩
    exact ⟨markerCount, ⟨certificate.transport ledgerPreserved⟩⟩
  case done =>
    rcases invariant with ⟨certificate⟩
    exact ⟨certificate.transport ledgerPreserved⟩
  all_goals trivial

/-- The candidate decoder is the only operation that changes the q16 ledger.
Every branch is accounted for: retry, sampler rejection, one more proven
noncompact record, or construction of the exact selected record. -/
theorem process_candidate_block_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (noRemainingMarker : remainingQ16MarkerCount remaining = 0)
    (history : Q16PriorNoncompactHistory environment counter
      snapshot.q16Candidates) :
    SnapshotQ16LedgerInvariant environment
      (processFutureFreeCandidateBlock environment snapshot base counter
        outputs remaining output nextCore) := by
  cases decoded : environment.decoders.candidate counter
      (outputs ++ [output]) with
  | none =>
      by_cases belowCap : outputs.length + 1 < 8
      · simp [SnapshotQ16LedgerInvariant, processFutureFreeCandidateBlock,
          decoded, belowCap, noRemainingMarker, history,
          remainingQ16MarkerCount]
      · simp [SnapshotQ16LedgerInvariant, processFutureFreeCandidateBlock,
          decoded, belowCap]
  | some outcome =>
      cases outcome with
      | samplerAbort =>
          simp [SnapshotQ16LedgerInvariant, processFutureFreeCandidateBlock,
            decoded]
      | schedule schedule =>
          by_cases compact : environment.frontierNodes schedule ≤ 203
          · have certificate :=
              compact_candidate_constructs_selected_q16_ledger environment
                snapshot base counter outputs remaining output nextCore schedule
                history decoded compact
            simpa [SnapshotQ16LedgerInvariant,
              processFutureFreeCandidateBlock, decoded, compact,
              noRemainingMarker, remainingQ16MarkerCount]
              using
                (show Nonempty (SelectedQ16LedgerCertificate environment
                    (processFutureFreeCandidateBlock environment snapshot base
                      counter outputs remaining output nextCore)) from
                  ⟨certificate⟩)
          · have noncompact : 203 < environment.frontierNodes schedule := by
              omega
            cases successor : nextQ16Counter? counter with
            | none =>
                simp [SnapshotQ16LedgerInvariant,
                  processFutureFreeCandidateBlock, decoded, compact,
                  successor]
            | some next =>
                have extended : Q16PriorNoncompactHistory environment next
                    (snapshot.q16Candidates ++
                      [decodedScheduleRecord counter schedule]) :=
                  .step (outputs ++ [output]) schedule history decoded
                    noncompact successor
                simpa [SnapshotQ16LedgerInvariant,
                  processFutureFreeCandidateBlock, decoded, compact,
                  successor, decodedScheduleRecord, noRemainingMarker,
                  remainingQ16MarkerCount] using extended

/-- Marking the selected q16 branch cannot lose its certificate when the
controller returns to the ordinary post-q16 schedule. -/
theorem selected_marker_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (schedule : QuerySchedule)
    (remaining : List FutureFreeSlot)
    (controlExact : snapshot.control =
      .q16Selected base counter schedule remaining)
    (invariant : SnapshotQ16LedgerInvariant environment snapshot) :
    SnapshotQ16LedgerInvariant environment
      { snapshot with control := linearOrDone remaining } := by
  have selectedData : remainingQ16MarkerCount remaining = 0 ∧
      Nonempty (SelectedQ16LedgerCertificate environment snapshot) := by
    simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
  have certificate := selectedData.2
  have noRemainingMarker := selectedData.1
  rcases certificate with ⟨certificate⟩
  let next : FutureFreeSnapshot :=
    { snapshot with control := linearOrDone remaining }
  have transported : SelectedQ16LedgerCertificate environment next :=
    certificate.transport rfl
  cases remaining with
  | nil => exact ⟨transported⟩
  | cons head tail => exact Or.inr ⟨noRemainingMarker, ⟨transported⟩⟩

/-- Returning to the ordinary schedule preserves the exact before/after-q16
phase.  In the empty-tail case the pre-q16 alternative is impossible, so
completion necessarily retains a selected certificate. -/
theorem linear_or_done_preserves_normal_q16_ledger_phase
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (remaining : List FutureFreeSlot)
    (phase : NormalQ16LedgerPhase environment remaining snapshot) :
    SnapshotQ16LedgerInvariant environment
      { snapshot with control := linearOrDone remaining } := by
  cases remaining with
  | nil =>
      rcases phase with ⟨markerCount, _empty⟩ |
        ⟨_markerCount, ⟨certificate⟩⟩
      · simp [remainingQ16MarkerCount] at markerCount
      · exact ⟨certificate.transport rfl⟩
  | cons head tail =>
      exact normal_q16_ledger_phase_transport
        (before := snapshot)
        (after := { snapshot with control := linearOrDone (head :: tail) })
        rfl phase

theorem complete_challenge_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (value : Qm31Bytes)
    (remaining : List FutureFreeSlot) (nextCore : RuntimeCore)
    (phase : NormalQ16LedgerPhase environment remaining snapshot) :
    SnapshotQ16LedgerInvariant environment
      (completeFutureFreeChallenge environment snapshot id value remaining
        nextCore) := by
  have ordinary :=
    linear_or_done_preserves_normal_q16_ledger_phase environment snapshot
      remaining phase
  cases id <;> simp only [completeFutureFreeChallenge]
  all_goals try
    exact snapshot_q16_ledger_invariant_transport
      (before := { snapshot with control := linearOrDone remaining })
      rfl rfl ordinary
  case circlePoint sample =>
    split
    · simp [SnapshotQ16LedgerInvariant]
    · exact snapshot_q16_ledger_invariant_transport
        (before := { snapshot with control := linearOrDone remaining })
        rfl rfl ordinary

/-- Challenge rejection sampling never changes the q16 ledger or skips the
unique q16 marker. -/
theorem process_challenge_block_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (phase : NormalQ16LedgerPhase environment remaining snapshot) :
    SnapshotQ16LedgerInvariant environment
      (processFutureFreeChallengeBlock environment snapshot id outputs
        remaining output nextCore) := by
  simp only [processFutureFreeChallengeBlock]
  split
  next value decoded =>
    exact complete_challenge_preserves_q16_ledger_invariant environment
      snapshot id value remaining nextCore phase
  next noValue =>
    split
    · exact normal_q16_ledger_phase_transport
        (before := snapshot) rfl phase
    · simp [SnapshotQ16LedgerInvariant]

/-- Consuming the unique q16 marker enters counter zero with the literal empty
candidate history. -/
theorem begin_q16_starts_empty_ledger_history
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (remaining : List FutureFreeSlot) (base : Digest256)
    (nextCore : RuntimeCore)
    (phase : NormalQ16LedgerPhase environment
      (.beginQ16 :: remaining) snapshot) :
    SnapshotQ16LedgerInvariant environment
      { snapshot with
        control := .q16Absorb base 0 remaining
        core := nextCore } := by
  rcases phase with ⟨markerCount, empty⟩ |
    ⟨markerCount, _certificate⟩
  · have noRemainingMarker : remainingQ16MarkerCount remaining = 0 := by
      simp [remainingQ16MarkerCount] at markerCount
      omega
    rw [SnapshotQ16LedgerInvariant, empty]
    exact ⟨noRemainingMarker, .start⟩
  · simp [remainingQ16MarkerCount] at markerCount

/-- A successful raw verifier reply preserves the proof-relevant q16 ledger
phase for every control constructor. -/
theorem after_verifier_reply_preserves_snapshot_q16_ledger
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (invariant : SnapshotQ16LedgerInvariant environment snapshot)
    (run : afterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    SnapshotQ16LedgerInvariant environment next := by
  cases controlExact : snapshot.control
  case adaptive control =>
    have empty : snapshot.q16Candidates = [] := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
    cases nextAdaptiveExact :
        control.afterVerifierReply environment.decoders reply with
    | none =>
        simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
          controlExact, nextAdaptiveExact] at run
    | some nextAdaptive =>
        simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
          controlExact, nextAdaptiveExact] at run
        subst next
        cases nextAdaptive <;>
          simp [SnapshotQ16LedgerInvariant, NormalQ16LedgerPhase,
            remainingQ16MarkerCount, fullFutureFreeSlots, empty]
        exact Or.inl (by decide)
  case linear remaining =>
    have phase : NormalQ16LedgerPhase environment remaining snapshot := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
    cases remaining with
    | nil =>
        cases reply <;>
          simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
            controlExact] at run
    | cons slot remaining =>
        cases slot <;> cases reply <;>
          simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
            controlExact] at run
        case fixed.none site =>
          subst next
          have tailPhase : NormalQ16LedgerPhase environment remaining
              snapshot := by
            simpa [NormalQ16LedgerPhase, remainingQ16MarkerCount] using phase
          have ordinary :=
            linear_or_done_preserves_normal_q16_ledger_phase environment
              snapshot remaining tailPhase
          exact snapshot_q16_ledger_invariant_transport
            (before := { snapshot with control := linearOrDone remaining })
            rfl rfl ordinary
        case fixed.single site output =>
          subst next
          have tailPhase : NormalQ16LedgerPhase environment remaining
              snapshot := by
            simpa [NormalQ16LedgerPhase, remainingQ16MarkerCount] using phase
          have ordinary :=
            linear_or_done_preserves_normal_q16_ledger_phase environment
              snapshot remaining tailPhase
          exact snapshot_q16_ledger_invariant_transport
            (before := { snapshot with control := linearOrDone remaining })
            rfl rfl ordinary
        case fixed.squeeze site output advance =>
          subst next
          have tailPhase : NormalQ16LedgerPhase environment remaining
              snapshot := by
            simpa [NormalQ16LedgerPhase, remainingQ16MarkerCount] using phase
          have ordinary :=
            linear_or_done_preserves_normal_q16_ledger_phase environment
              snapshot remaining tailPhase
          exact snapshot_q16_ledger_invariant_transport
            (before := { snapshot with control := linearOrDone remaining })
            rfl rfl ordinary
        case challenge.squeeze id output advance =>
          subst next
          have tailPhase : NormalQ16LedgerPhase environment remaining
              snapshot := by
            simpa [NormalQ16LedgerPhase, remainingQ16MarkerCount] using phase
          have processed :=
            process_challenge_block_preserves_q16_ledger_invariant
              environment snapshot id [] remaining output nextCore tailPhase
          exact snapshot_q16_ledger_invariant_transport
            (before := processFutureFreeChallengeBlock environment snapshot id
              [] remaining output nextCore) rfl rfl processed
        case beginQ16.none =>
          subst next
          exact begin_q16_starts_empty_ledger_history environment snapshot
            remaining nextCore.digest nextCore phase
  case absorbPayload payload remaining =>
    have phase : NormalQ16LedgerPhase environment remaining snapshot := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case single output =>
      subst next
      have ordinary :=
        linear_or_done_preserves_normal_q16_ledger_phase environment snapshot
          remaining phase
      exact snapshot_q16_ledger_invariant_transport
        (before := { snapshot with control := linearOrDone remaining })
        rfl rfl ordinary
  case workCheck stage nonce remaining =>
    have phase : NormalQ16LedgerPhase environment remaining snapshot := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case single output =>
      subst next
      exact normal_q16_ledger_phase_transport
        (before := snapshot) rfl phase
  case workCheckpoint stage nonce remaining =>
    have phase : NormalQ16LedgerPhase environment remaining snapshot := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case none =>
      subst next
      exact normal_q16_ledger_phase_transport
        (before := snapshot) rfl phase
  case workAbsorb stage nonce remaining =>
    have phase : NormalQ16LedgerPhase environment remaining snapshot := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case single output =>
      subst next
      have ordinary :=
        linear_or_done_preserves_normal_q16_ledger_phase environment snapshot
          remaining phase
      exact snapshot_q16_ledger_invariant_transport
        (before := { snapshot with control := linearOrDone remaining })
        rfl rfl ordinary
  case sampleChallenge id outputs remaining =>
    have phase : NormalQ16LedgerPhase environment remaining snapshot := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case squeeze output advance =>
      subst next
      have processed := process_challenge_block_preserves_q16_ledger_invariant
        environment snapshot id outputs remaining output nextCore phase
      exact snapshot_q16_ledger_invariant_transport
        (before := processFutureFreeChallengeBlock environment snapshot id
          outputs remaining output nextCore) rfl rfl processed
  case q16Absorb base counter remaining =>
    have phase : remainingQ16MarkerCount remaining = 0 ∧
        Q16PriorNoncompactHistory environment counter
          snapshot.q16Candidates := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case single output => subst next; exact phase
  case q16Sample base counter outputs remaining =>
    have phase : remainingQ16MarkerCount remaining = 0 ∧
        Q16PriorNoncompactHistory environment counter
          snapshot.q16Candidates := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case squeeze output advance =>
      let processed := processFutureFreeCandidateBlock environment snapshot
        base counter outputs remaining output nextCore
      have processedInvariant :
          SnapshotQ16LedgerInvariant environment processed :=
        process_candidate_block_preserves_q16_ledger_invariant environment
          snapshot base counter outputs remaining output nextCore phase.1 phase.2
      subst next
      exact snapshot_q16_ledger_invariant_transport
        (before := processed) rfl rfl processedInvariant
  case q16Restore base counter nextCounter remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case none =>
      cases nextCounter with
      | none =>
          subst next
          trivial
      | some nextCounter =>
          have phase : remainingQ16MarkerCount remaining = 0 ∧
              Q16PriorNoncompactHistory environment nextCounter
                snapshot.q16Candidates := by
            simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
          subst next
          exact phase
  case q16Selected base counter schedule remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case none =>
      have phaseInvariant :=
        selected_marker_preserves_q16_ledger_invariant environment snapshot
          base counter schedule remaining controlExact invariant
      subst next
      exact snapshot_q16_ledger_invariant_transport
        (before := { snapshot with control := linearOrDone remaining })
        rfl rfl phaseInvariant
  all_goals
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact, SnapshotQ16LedgerInvariant] at run ⊢
    all_goals subst next <;> trivial

/-! ## Literal q16 verifier replies -/

theorem q16_absorb_reply_preserves_snapshot_q16_ledger
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64)
    (remaining : List FutureFreeSlot) (reply : VerifierReply)
    (nextCore : RuntimeCore)
    (controlExact : snapshot.control = .q16Absorb base counter remaining)
    (invariant : SnapshotQ16LedgerInvariant environment snapshot)
    (run : afterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    SnapshotQ16LedgerInvariant environment next := by
  have phase : remainingQ16MarkerCount remaining = 0 ∧
      Q16PriorNoncompactHistory environment counter
        snapshot.q16Candidates := by
    simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
  cases reply <;>
    simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      controlExact] at run
  case single output =>
    subst next
    exact phase

theorem q16_sample_reply_preserves_snapshot_q16_ledger
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output advance : Digest256)
    (nextCore : RuntimeCore)
    (controlExact : snapshot.control =
      .q16Sample base counter outputs remaining)
    (invariant : SnapshotQ16LedgerInvariant environment snapshot)
    (run : afterFutureFreeVerifierReply environment snapshot
      (.squeeze output advance) nextCore = some next) :
    SnapshotQ16LedgerInvariant environment next := by
  have phase : remainingQ16MarkerCount remaining = 0 ∧
      Q16PriorNoncompactHistory environment counter
        snapshot.q16Candidates := by
    simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant
  let processed := processFutureFreeCandidateBlock environment snapshot base
    counter outputs remaining output nextCore
  have processedInvariant : SnapshotQ16LedgerInvariant environment processed :=
    process_candidate_block_preserves_q16_ledger_invariant environment snapshot
      base counter outputs remaining output nextCore phase.1 phase.2
  simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
    controlExact, processed] at run
  subst next
  exact snapshot_q16_ledger_invariant_transport
    (before := processed)
    (after := { processed with bindings := snapshot.bindings })
    rfl rfl processedInvariant

theorem q16_restore_reply_preserves_snapshot_q16_ledger
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (nextCounter : Option (Fin 64))
    (remaining : List FutureFreeSlot) (nextCore : RuntimeCore)
    (controlExact : snapshot.control =
      .q16Restore base counter nextCounter remaining)
    (invariant : SnapshotQ16LedgerInvariant environment snapshot)
    (run : afterFutureFreeVerifierReply environment snapshot .none nextCore =
      some next) :
    SnapshotQ16LedgerInvariant environment next := by
  cases successor : nextCounter with
  | none =>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact, successor] at run
      subst next
      trivial
  | some nextCounter =>
      have phase : remainingQ16MarkerCount remaining = 0 ∧
          Q16PriorNoncompactHistory environment nextCounter
            snapshot.q16Candidates := by
        simpa [SnapshotQ16LedgerInvariant, controlExact, successor] using
          invariant
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact, successor] at run
      subst next
      exact phase

theorem q16_selected_reply_preserves_snapshot_q16_ledger
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (schedule : QuerySchedule)
    (remaining : List FutureFreeSlot) (nextCore : RuntimeCore)
    (controlExact : snapshot.control =
      .q16Selected base counter schedule remaining)
    (invariant : SnapshotQ16LedgerInvariant environment snapshot)
    (run : afterFutureFreeVerifierReply environment snapshot .none nextCore =
      some next) :
    SnapshotQ16LedgerInvariant environment next := by
  let phaseSnapshot : FutureFreeSnapshot :=
    { snapshot with control := linearOrDone remaining }
  have phaseInvariant : SnapshotQ16LedgerInvariant environment phaseSnapshot :=
    selected_marker_preserves_q16_ledger_invariant environment snapshot base
      counter schedule remaining controlExact invariant
  simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
    controlExact] at run
  subst next
  exact snapshot_q16_ledger_invariant_transport
    (before := phaseSnapshot)
    (after := { snapshot with
      control := linearOrDone remaining
      core := nextCore }) rfl rfl phaseInvariant

/-! ## Complete-state and restoration closure -/

/-- The live snapshot and every complete snapshot retained for restoration
carry the proof-relevant ledger phase. -/
def FutureFreeQ16LedgerInvariant (environment : FutureFreeEnvironment)
    (state : FutureFreeVerifierState) : Prop :=
  SnapshotQ16LedgerInvariant environment state.current ∧
    ∀ snapshot ∈ state.seen,
      SnapshotQ16LedgerInvariant environment snapshot

@[simp] theorem initial_future_free_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (bindings : FixedBindings) :
    FutureFreeQ16LedgerInvariant environment
      (initialFutureFreeVerifierState bindings) := by
  simp [FutureFreeQ16LedgerInvariant, initialFutureFreeVerifierState]

/-- Appending a locally valid next snapshot preserves the complete-history
ledger invariant. -/
theorem append_future_free_snapshot_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (state : FutureFreeVerifierState)
    (event : FutureFreeEvent) (next : FutureFreeSnapshot)
    (invariant : FutureFreeQ16LedgerInvariant environment state)
    (nextInvariant : SnapshotQ16LedgerInvariant environment next) :
    FutureFreeQ16LedgerInvariant environment
      (appendFutureFreeSnapshot state event next) := by
  constructor
  · exact nextInvariant
  · intro snapshot member
    simp only [appendFutureFreeSnapshot, List.mem_append,
      List.mem_singleton] at member
    rcases member with old | rfl
    · exact invariant.2 snapshot old
    · exact nextInvariant

/-- Every literal raw prover submission preserves the ledger phase.  Payload
and work submissions merely expose the next non-q16 control and cannot alter
the candidate ledger. -/
theorem submit_next_raw_message_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (invariant : FutureFreeQ16LedgerInvariant environment state)
    (submitted : submitNextRawMessage raw state = some next) :
    FutureFreeQ16LedgerInvariant environment next := by
  unfold submitNextRawMessage at submitted
  split at submitted
  next controlExact =>
    unfold submitFutureFreeC1 at submitted
    split at submitted
    next =>
      have nextExact := Option.some.inj submitted
      rw [← nextExact]
      apply append_future_free_snapshot_preserves_q16_ledger_invariant
        environment state _ _ invariant
      have empty : state.current.q16Candidates = [] := by
        simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant.1
      simpa [SnapshotQ16LedgerInvariant, empty]
    all_goals simp at submitted
  next lambda chi controlExact =>
    have nextExact := Option.some.inj submitted
    rw [← nextExact]
    apply append_future_free_snapshot_preserves_q16_ledger_invariant
      environment state _ _ invariant
    have empty : state.current.q16Candidates = [] := by
      simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant.1
    simpa [submitFutureFreeC2, SnapshotQ16LedgerInvariant, empty]
  next site remaining controlExact =>
    unfold submitFutureFreePayload at submitted
    split at submitted
    next _control site' remaining' controlExact' =>
      split at submitted
      next =>
        have branchExact : site = site' ∧ remaining = remaining' := by
          have controlsEqual := controlExact.symm.trans controlExact'
          simpa using controlsEqual
        rcases branchExact with ⟨rfl, rfl⟩
        have nextExact := Option.some.inj submitted
        rw [← nextExact]
        apply append_future_free_snapshot_preserves_q16_ledger_invariant
          environment state _ _ invariant
        have phase : NormalQ16LedgerPhase environment
            (.payload site :: remaining) state.current := by
          simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant.1
        simpa [SnapshotQ16LedgerInvariant] using
          (normal_q16_ledger_phase_transport
            (environment := environment)
            (before := state.current)
            (after := { state.current with
              control := .absorbPayload (rawPayloadAt raw site) remaining
              receivedPayloads := state.current.receivedPayloads ++
                [rawPayloadAt raw site] })
            rfl (by
              simpa [NormalQ16LedgerPhase, remainingQ16MarkerCount] using
                phase))
      next => simp at submitted
    all_goals simp at submitted
  next stage remaining controlExact =>
    unfold submitFutureFreeWorkNonce at submitted
    split at submitted
    next _control stage' remaining' controlExact' =>
      have branchExact : stage = stage' ∧ remaining = remaining' := by
        have controlsEqual := controlExact.symm.trans controlExact'
        simpa using controlsEqual
      rcases branchExact with ⟨rfl, rfl⟩
      have nextExact := Option.some.inj submitted
      rw [← nextExact]
      apply append_future_free_snapshot_preserves_q16_ledger_invariant
        environment state _ _ invariant
      have phase : NormalQ16LedgerPhase environment
          (.work stage :: remaining) state.current := by
        simpa [SnapshotQ16LedgerInvariant, controlExact] using invariant.1
      simpa [SnapshotQ16LedgerInvariant] using
        (normal_q16_ledger_phase_transport
          (environment := environment)
          (before := state.current)
          (after := { state.current with
            control := .workCheck stage (rawWorkNonceAt raw stage) remaining })
          rfl (by
            simpa [NormalQ16LedgerPhase, remainingQ16MarkerCount] using phase))
    all_goals simp at submitted
  all_goals simp at submitted

/-- A successful complete verifier advance appends a locally valid snapshot,
so both the live state and retained restoration history remain valid. -/
theorem advance_future_free_verifier_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (invariant : FutureFreeQ16LedgerInvariant environment state)
    (run : advanceFutureFreeVerifier environment state reply = some next) :
    FutureFreeQ16LedgerInvariant environment next := by
  rw [advanceFutureFreeVerifier] at run
  obtain ⟨action, _actionExact, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextCore, _coreExact, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextSnapshot, snapshotExact, finalExact⟩ :=
    Option.bind_eq_some_iff.mp run
  have nextSnapshotInvariant :=
    after_verifier_reply_preserves_snapshot_q16_ledger environment
      state.current nextSnapshot reply nextCore invariant.1 snapshotExact
  have nextExact := Option.some.inj finalExact
  subst next
  exact append_future_free_snapshot_preserves_q16_ledger_invariant
    environment state (.verifier action reply) nextSnapshot invariant
      nextSnapshotInvariant

/-- One literal driver microstep preserves the complete q16 ledger
invariant, independently of how many oracle pairs the verifier action uses. -/
theorem future_free_operational_step_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (step : FutureFreeOperationalStep environment raw state pairs next)
    (invariant : FutureFreeQ16LedgerInvariant environment state) :
    FutureFreeQ16LedgerInvariant environment next := by
  cases step with
  | prover submitted event snapshot appendExact =>
      exact submit_next_raw_message_preserves_q16_ledger_invariant
        environment raw state next invariant submitted
  | verifier forced replyPath advanced =>
      exact advance_future_free_verifier_preserves_q16_ledger_invariant
        environment state next _ invariant advanced
  | stutter noSubmission noAction => exact invariant

/-- The invariant therefore holds across an arbitrary finite literal
future-free execution. -/
theorem future_free_operational_trace_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state final : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (trace : FutureFreeOperationalTrace environment raw state pairs final)
    (invariant : FutureFreeQ16LedgerInvariant environment state) :
    FutureFreeQ16LedgerInvariant environment final := by
  induction trace with
  | stop current => exact invariant
  | next step rest inductionHypothesis =>
      exact inductionHypothesis
        (future_free_operational_step_preserves_q16_ledger_invariant
          environment raw _ _ _ step invariant)

/-- Restoring a literal transition keeps the exact phase stored on its
previously-seen `before` snapshot. -/
theorem restore_indexed_transition_preserves_q16_ledger_invariant
    (environment : FutureFreeEnvironment) (state : FutureFreeVerifierState)
    (transition : FutureFreeTransition)
    (invariant : FutureFreeQ16LedgerInvariant environment state)
    (closed : FutureFreeHistoryClosed state)
    (member : transition ∈ state.transitions) :
    FutureFreeQ16LedgerInvariant environment
      (restoreIndexedTransition transition) := by
  have beforeSeen : transition.before ∈ state.seen :=
    (closed.2.2 transition member).1
  have beforeInvariant := invariant.2 transition.before beforeSeen
  exact ⟨beforeInvariant, by
    intro snapshot seen
    simp [restoreIndexedTransition] at seen
    subst snapshot
    exact beforeInvariant⟩

/-- Completion is strong: unlike an explicit rejection control, `.done`
contains an actual selected first-compact certificate. -/
theorem done_state_has_selected_q16_ledger
    (environment : FutureFreeEnvironment) (state : FutureFreeVerifierState)
    (invariant : FutureFreeQ16LedgerInvariant environment state)
    (done : state.current.control = .done) :
    Nonempty (SelectedQ16LedgerCertificate environment state.current) := by
  simpa [SnapshotQ16LedgerInvariant, done] using invariant.1

#print axioms initial_snapshot_q16_ledger_invariant
#print axioms selected_certificate_of_ledger_preserved
#print axioms normal_q16_ledger_phase_transport
#print axioms snapshot_q16_ledger_invariant_transport
#print axioms process_candidate_block_preserves_q16_ledger_invariant
#print axioms selected_marker_preserves_q16_ledger_invariant
#print axioms q16_absorb_reply_preserves_snapshot_q16_ledger
#print axioms q16_sample_reply_preserves_snapshot_q16_ledger
#print axioms q16_restore_reply_preserves_snapshot_q16_ledger
#print axioms q16_selected_reply_preserves_snapshot_q16_ledger
#print axioms initial_future_free_q16_ledger_invariant
#print axioms append_future_free_snapshot_preserves_q16_ledger_invariant
#print axioms submit_next_raw_message_preserves_q16_ledger_invariant
#print axioms advance_future_free_verifier_preserves_q16_ledger_invariant
#print axioms future_free_operational_step_preserves_q16_ledger_invariant
#print axioms future_free_operational_trace_preserves_q16_ledger_invariant
#print axioms restore_indexed_transition_preserves_q16_ledger_invariant
#print axioms done_state_has_selected_q16_ledger

end

end AspisK1.V7Tag73Q16LedgerControlInvariant
