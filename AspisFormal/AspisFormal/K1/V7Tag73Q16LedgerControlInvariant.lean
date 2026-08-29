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

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73Q16LedgerCertificate
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
#print axioms restore_indexed_transition_preserves_q16_ledger_invariant
#print axioms done_state_has_selected_q16_ledger

end

end AspisK1.V7Tag73Q16LedgerControlInvariant
