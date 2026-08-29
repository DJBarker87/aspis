import AspisFormal.K1.V7Tag73RawFutureFreeDriver
import AspisFormal.K1.V7Tag73SamplerExactValue
import AspisFormal.K1.V7Tag73ConcreteRestorationClient

/-!
# Exact gamma/alpha-zero records in the executable Tag-73 controller

The restored K1.3 view must not accept caller-supplied Fiat--Shamir
challenges.  This file tracks the two values used by the one-fold decoder
through the literal future-free controller.  Before a challenge slot is
consumed it remains in the exact pending schedule; afterwards the verifier's
append-only decoded-challenge ledger contains a canonical exact-tower value.

The invariant is restoration stable because it is attached to the live
snapshot and every snapshot retained in `seen`.  It contains no probability,
knowledge, or source-code premise.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ChallengeRecordControlInvariant

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7FsAokExperiment
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A challenge record produced by the executable sampler has a canonical
value in the literal QM31 tower. -/
def ExactRecordedChallenge (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) : Prop :=
  ∃ encoded : Qm31Bytes, ∃ value : QM31Exact,
    { id := id, value := encoded } ∈ snapshot.decodedChallenges ∧
      decodeTagQM31ExactLE encoded = some value

/-- While a target challenge has not yet been sampled, its exact slot must
remain in the controller schedule.  Once consumed, its exact decoded record
must be present. -/
def PendingOrRecorded (snapshot : FutureFreeSnapshot)
    (remaining : List FutureFreeSlot) (id : ChallengeId) : Prop :=
  .challenge id ∈ remaining ∨ ExactRecordedChallenge snapshot id

def RequiredK13ChallengeRecords (snapshot : FutureFreeSnapshot)
    (remaining : List FutureFreeSlot) : Prop :=
  PendingOrRecorded snapshot remaining .gamma ∧
    PendingOrRecorded snapshot remaining (.alpha 0)

/-- The virtual pending schedule of each non-rejecting controller phase.
`sampleChallenge` retains its in-progress slot until a successful decode.
Adaptive and explicit rejection states impose no K1.3 terminal obligation. -/
def controlPendingSlots : FutureFreeControl → Option (List FutureFreeSlot)
  | .adaptive _ => none
  | .linear remaining => some remaining
  | .absorbPayload _ remaining => some remaining
  | .workCheck _ _ remaining => some remaining
  | .workCheckpoint _ _ remaining => some remaining
  | .workAbsorb _ _ remaining => some remaining
  | .sampleChallenge id _ remaining => some (.challenge id :: remaining)
  | .q16Absorb _ _ remaining => some remaining
  | .q16Sample _ _ _ remaining => some remaining
  | .q16Restore _ _ _ remaining => some remaining
  | .q16Selected _ _ _ remaining => some remaining
  | .q16SamplerReject _ _ => none
  | .q16AllNoncompactReject => none
  | .rejected _ => none
  | .done => some []

def SnapshotK13ChallengeInvariant (snapshot : FutureFreeSnapshot) : Prop :=
  match controlPendingSlots snapshot.control with
  | none => True
  | some remaining => RequiredK13ChallengeRecords snapshot remaining

@[simp] theorem initial_snapshot_k13_challenge_invariant
    (bindings : FixedBindings) :
    SnapshotK13ChallengeInvariant (initialFutureFreeSnapshot bindings) := by
  simp [SnapshotK13ChallengeInvariant, initialFutureFreeSnapshot,
    controlPendingSlots]

theorem exact_recorded_challenge_transport
    {before after : FutureFreeSnapshot} {id : ChallengeId}
    (recordsExact : after.decodedChallenges = before.decodedChallenges)
    (recorded : ExactRecordedChallenge before id) :
    ExactRecordedChallenge after id := by
  rcases recorded with ⟨encoded, value, member, decoded⟩
  exact ⟨encoded, value, by simpa [recordsExact] using member, decoded⟩

theorem required_k13_challenge_records_transport
    {before after : FutureFreeSnapshot} {remaining : List FutureFreeSlot}
    (recordsExact : after.decodedChallenges = before.decodedChallenges)
    (required : RequiredK13ChallengeRecords before remaining) :
    RequiredK13ChallengeRecords after remaining := by
  constructor
  · rcases required.1 with pending | recorded
    · exact Or.inl pending
    · exact Or.inr (exact_recorded_challenge_transport recordsExact recorded)
  · rcases required.2 with pending | recorded
    · exact Or.inl pending
    · exact Or.inr (exact_recorded_challenge_transport recordsExact recorded)

theorem snapshot_k13_challenge_invariant_transport
    {before after : FutureFreeSnapshot}
    (controlExact : after.control = before.control)
    (recordsExact : after.decodedChallenges = before.decodedChallenges)
    (invariant : SnapshotK13ChallengeInvariant before) :
    SnapshotK13ChallengeInvariant after := by
  unfold SnapshotK13ChallengeInvariant at invariant ⊢
  rw [controlExact]
  cases pending : controlPendingSlots before.control with
  | none => trivial
  | some remaining =>
      rw [pending] at invariant
      exact required_k13_challenge_records_transport recordsExact invariant

/-- Appending a different decoded record preserves an earlier exact record. -/
theorem exact_recorded_challenge_append_old
    (snapshot : FutureFreeSnapshot) (newId target : ChallengeId)
    (encoded : Qm31Bytes)
    (recorded : ExactRecordedChallenge snapshot target) :
    ExactRecordedChallenge
      { snapshot with decodedChallenges :=
          snapshot.decodedChallenges ++ [{ id := newId, value := encoded }] }
      target := by
  rcases recorded with ⟨oldBytes, value, member, decoded⟩
  exact ⟨oldBytes, value, List.mem_append_left _ member, decoded⟩

/-- A successful exact sampler decode creates the target's exact record. -/
theorem exact_recorded_challenge_append_new
    (snapshot : FutureFreeSnapshot) (id : ChallengeId)
    (encoded : Qm31Bytes) (value : QM31Exact)
    (decoded : decodeTagQM31ExactLE encoded = some value) :
    ExactRecordedChallenge
      { snapshot with decodedChallenges :=
          snapshot.decodedChallenges ++ [{ id := id, value := encoded }] }
      id := by
  exact ⟨encoded, value, by simp, decoded⟩

theorem pending_or_recorded_after_successful_challenge
    (snapshot : FutureFreeSnapshot) (id target : ChallengeId)
    (encoded : Qm31Bytes) (value : QM31Exact)
    (remaining : List FutureFreeSlot)
    (decoded : decodeTagQM31ExactLE encoded = some value)
    (before : PendingOrRecorded snapshot (.challenge id :: remaining) target) :
    PendingOrRecorded
      { snapshot with decodedChallenges :=
          snapshot.decodedChallenges ++ [{ id := id, value := encoded }] }
      remaining target := by
  rcases before with pending | recorded
  · simp only [List.mem_cons, FutureFreeSlot.challenge.injEq] at pending
    rcases pending with rfl | stillPending
    · exact Or.inr
        (exact_recorded_challenge_append_new snapshot target encoded value
          decoded)
    · exact Or.inl stillPending
  · exact Or.inr
      (exact_recorded_challenge_append_old snapshot id target encoded recorded)

theorem required_after_successful_challenge
    (snapshot : FutureFreeSnapshot) (id : ChallengeId)
    (encoded : Qm31Bytes) (value : QM31Exact)
    (remaining : List FutureFreeSlot)
    (decoded : decodeTagQM31ExactLE encoded = some value)
    (before : RequiredK13ChallengeRecords snapshot
      (.challenge id :: remaining)) :
    RequiredK13ChallengeRecords
      { snapshot with decodedChallenges :=
          snapshot.decodedChallenges ++ [{ id := id, value := encoded }] }
      remaining := by
  exact ⟨
    pending_or_recorded_after_successful_challenge snapshot id .gamma encoded
      value remaining decoded before.1,
    pending_or_recorded_after_successful_challenge snapshot id (.alpha 0)
      encoded value remaining decoded before.2⟩

/-- `linearOrDone` consumes no challenge slot by itself. -/
theorem linear_or_done_has_required_challenge_records
    (snapshot : FutureFreeSnapshot) (remaining : List FutureFreeSlot)
    (required : RequiredK13ChallengeRecords snapshot remaining) :
    SnapshotK13ChallengeInvariant
      { snapshot with control := linearOrDone remaining } := by
  cases remaining with
  | nil => exact required
  | cons head tail => exact required

/-- The only ledger-changing ordinary transition is a successful sampler
decode.  Its exact-tower value is supplied by the already kernel-checked
deployed sampler theorem. -/
theorem process_challenge_block_preserves_k13_challenge_invariant
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (required : RequiredK13ChallengeRecords snapshot
      (.challenge id :: remaining)) :
    SnapshotK13ChallengeInvariant
      (processFutureFreeChallengeBlock environment snapshot id outputs
        remaining output nextCore) := by
  simp only [processFutureFreeChallengeBlock]
  split
  next encoded accepted =>
    obtain ⟨value, decoded⟩ :=
      decodeChallengeParameter_has_exact_tower_value
        exactSecureCircleParameterMap id (outputs ++ [output]) encoded
        (by simpa [FutureFreeEnvironment.decoders] using accepted)
    have afterAppend := required_after_successful_challenge snapshot id
      encoded value remaining decoded required
    let completedBase : FutureFreeSnapshot :=
      { snapshot with
        core := nextCore
        decodedChallenges := snapshot.decodedChallenges ++
          [{ id := id, value := encoded }] }
    have completedRequired :
        RequiredK13ChallengeRecords completedBase remaining :=
      required_k13_challenge_records_transport rfl afterAppend
    have ordinary := linear_or_done_has_required_challenge_records
      completedBase remaining completedRequired
    cases id <;> simp only [completeFutureFreeChallenge]
    all_goals try simpa [completedBase] using ordinary
    case circlePoint sample =>
      split
      · trivial
      · exact snapshot_k13_challenge_invariant_transport
          (before := { completedBase with control := linearOrDone remaining })
          (after := { snapshot with
            control := linearOrDone remaining
            core := nextCore
            decodedChallenges := snapshot.decodedChallenges ++
              [{ id := .circlePoint sample, value := encoded }]
            circlePoints := snapshot.circlePoints ++ [_] })
          rfl rfl ordinary
  next noValue =>
    split
    · exact required
    · trivial

theorem process_candidate_block_preserves_k13_challenge_invariant
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (required : RequiredK13ChallengeRecords snapshot remaining) :
    SnapshotK13ChallengeInvariant
      (processFutureFreeCandidateBlock environment snapshot base counter
        outputs remaining output nextCore) := by
  cases decoded : environment.decoders.candidate counter
      (outputs ++ [output]) with
  | none =>
      by_cases belowCap : outputs.length + 1 < 8
      · have transported := required_k13_challenge_records_transport
          (before := snapshot)
          (after := { snapshot with
            control := .q16Sample base counter (outputs ++ [output]) remaining
            core := nextCore }) rfl required
        simpa [processFutureFreeCandidateBlock, decoded, belowCap,
          SnapshotK13ChallengeInvariant, controlPendingSlots] using transported
      · simp [processFutureFreeCandidateBlock, decoded, belowCap,
          SnapshotK13ChallengeInvariant, controlPendingSlots]
  | some outcome =>
      cases outcome with
      | samplerAbort =>
          simp [processFutureFreeCandidateBlock, decoded,
            SnapshotK13ChallengeInvariant, controlPendingSlots]
      | schedule schedule =>
          by_cases compact : environment.frontierNodes schedule ≤ 203
          · have transported := required_k13_challenge_records_transport
              (before := snapshot)
              (after := { snapshot with
                control := .q16Selected base counter schedule remaining
                core := nextCore
                q16Candidates := snapshot.q16Candidates ++
                  [{ counter := counter, outcome := .schedule schedule }] })
              rfl required
            simpa [processFutureFreeCandidateBlock, decoded, compact,
              SnapshotK13ChallengeInvariant, controlPendingSlots] using
                transported
          · have transported := required_k13_challenge_records_transport
              (before := snapshot)
              (after := { snapshot with
                control := .q16Restore base counter (nextQ16Counter? counter)
                  remaining
                core := nextCore
                q16Candidates := snapshot.q16Candidates ++
                  [{ counter := counter, outcome := .schedule schedule }] })
              rfl required
            simpa [processFutureFreeCandidateBlock, decoded, compact,
              SnapshotK13ChallengeInvariant, controlPendingSlots] using
                transported

/-! ## Complete-state and operational preservation -/

theorem after_verifier_reply_preserves_snapshot_k13_challenges
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (invariant : SnapshotK13ChallengeInvariant snapshot)
    (run : afterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    SnapshotK13ChallengeInvariant next := by
  cases controlExact : snapshot.control
  case adaptive control =>
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
          simp [SnapshotK13ChallengeInvariant, controlPendingSlots,
            RequiredK13ChallengeRecords, PendingOrRecorded,
            fullFutureFreeSlots, beforeQ16Slots]
  case linear remaining =>
    cases remaining with
    | nil =>
        cases reply <;>
          simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
            controlExact] at run
    | cons slot remaining =>
        cases slot <;> cases reply <;>
          simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
            controlExact] at run
        case fixed.none action =>
          subst next
          have required : RequiredK13ChallengeRecords snapshot remaining := by
            simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
              controlExact, RequiredK13ChallengeRecords, PendingOrRecorded]
              using invariant
          exact snapshot_k13_challenge_invariant_transport
            (before := { snapshot with control := linearOrDone remaining })
            rfl rfl
            (linear_or_done_has_required_challenge_records snapshot remaining
              required)
        case fixed.single action output =>
          subst next
          have required : RequiredK13ChallengeRecords snapshot remaining := by
            simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
              controlExact, RequiredK13ChallengeRecords, PendingOrRecorded]
              using invariant
          exact snapshot_k13_challenge_invariant_transport
            (before := { snapshot with control := linearOrDone remaining })
            rfl rfl
            (linear_or_done_has_required_challenge_records snapshot remaining
              required)
        case fixed.squeeze action output advance =>
          subst next
          have required : RequiredK13ChallengeRecords snapshot remaining := by
            simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
              controlExact, RequiredK13ChallengeRecords, PendingOrRecorded]
              using invariant
          exact snapshot_k13_challenge_invariant_transport
            (before := { snapshot with control := linearOrDone remaining })
            rfl rfl
            (linear_or_done_has_required_challenge_records snapshot remaining
              required)
        case challenge.squeeze id output advance =>
          subst next
          have required : RequiredK13ChallengeRecords snapshot
              (.challenge id :: remaining) := by
            simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
              controlExact] using invariant
          exact snapshot_k13_challenge_invariant_transport
            (before := processFutureFreeChallengeBlock environment snapshot id
              [] remaining output nextCore) rfl rfl
            (process_challenge_block_preserves_k13_challenge_invariant
              environment snapshot id [] remaining output nextCore required)
        case beginQ16.none =>
          subst next
          have required : RequiredK13ChallengeRecords snapshot remaining := by
            simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
              controlExact, RequiredK13ChallengeRecords, PendingOrRecorded]
              using invariant
          simpa [SnapshotK13ChallengeInvariant, controlPendingSlots] using
            (required_k13_challenge_records_transport
              (before := snapshot) (after := { snapshot with
                control := .q16Absorb nextCore.digest 0 remaining
                core := nextCore }) rfl required)
  case absorbPayload payload remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case single output =>
      subst next
      have required : RequiredK13ChallengeRecords snapshot remaining := by
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
          controlExact] using invariant
      exact snapshot_k13_challenge_invariant_transport
        (before := { snapshot with control := linearOrDone remaining })
        rfl rfl
        (linear_or_done_has_required_challenge_records snapshot remaining
          required)
  case workCheck stage nonce remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case single output =>
      subst next
      have required : RequiredK13ChallengeRecords snapshot remaining := by
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
          controlExact] using invariant
      simpa [SnapshotK13ChallengeInvariant, controlPendingSlots] using
        (required_k13_challenge_records_transport
          (before := snapshot) (after := { snapshot with
            control := .workCheckpoint stage nonce remaining
            core := nextCore
            checkedWorkNonces := snapshot.checkedWorkNonces ++
              [{ stage := stage, nonce := nonce }] }) rfl required)
  case workCheckpoint stage nonce remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case none =>
      subst next
      have required : RequiredK13ChallengeRecords snapshot remaining := by
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
          controlExact] using invariant
      simpa [SnapshotK13ChallengeInvariant, controlPendingSlots] using
        (required_k13_challenge_records_transport
          (before := snapshot) (after := { snapshot with
            control := .workAbsorb stage nonce remaining
            core := nextCore }) rfl required)
  case workAbsorb stage nonce remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case single output =>
      subst next
      have required : RequiredK13ChallengeRecords snapshot remaining := by
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
          controlExact] using invariant
      exact snapshot_k13_challenge_invariant_transport
        (before := { snapshot with control := linearOrDone remaining })
        rfl rfl
        (linear_or_done_has_required_challenge_records snapshot remaining
          required)
  case sampleChallenge id outputs remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case squeeze output advance =>
      subst next
      have required : RequiredK13ChallengeRecords snapshot
          (.challenge id :: remaining) := by
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
          controlExact] using invariant
      exact snapshot_k13_challenge_invariant_transport
        (before := processFutureFreeChallengeBlock environment snapshot id
          outputs remaining output nextCore) rfl rfl
        (process_challenge_block_preserves_k13_challenge_invariant environment
          snapshot id outputs remaining output nextCore required)
  case q16Selected base counter schedule remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case none =>
      subst next
      have required : RequiredK13ChallengeRecords snapshot remaining := by
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
          controlExact] using invariant
      exact snapshot_k13_challenge_invariant_transport
        (before := { snapshot with control := linearOrDone remaining })
        rfl rfl
        (linear_or_done_has_required_challenge_records snapshot remaining
          required)
  case q16Absorb base counter remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case single output =>
      subst next
      have required : RequiredK13ChallengeRecords snapshot remaining := by
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
          controlExact] using invariant
      simpa [SnapshotK13ChallengeInvariant, controlPendingSlots] using
        (required_k13_challenge_records_transport
          (before := snapshot) (after := { snapshot with
            control := .q16Sample base counter [] remaining
            core := nextCore }) rfl required)
  case q16Sample base counter outputs remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case squeeze output advance =>
      subst next
      have required : RequiredK13ChallengeRecords snapshot remaining := by
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
          controlExact] using invariant
      exact snapshot_k13_challenge_invariant_transport
        (before := processFutureFreeCandidateBlock environment snapshot base
          counter outputs remaining output nextCore) rfl rfl
        (process_candidate_block_preserves_k13_challenge_invariant environment
          snapshot base counter outputs remaining output nextCore required)
  case q16Restore base counter nextCounter remaining =>
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact] at run
    case none =>
      subst next
      cases nextCounter with
      | none => trivial
      | some nextCounter =>
          have required : RequiredK13ChallengeRecords snapshot remaining := by
            simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
              controlExact] using invariant
          simpa [SnapshotK13ChallengeInvariant, controlPendingSlots] using
            (required_k13_challenge_records_transport
              (before := snapshot) (after := { snapshot with
                control := .q16Absorb base nextCounter remaining
                core := nextCore }) rfl required)
  all_goals
    cases reply <;>
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        controlExact, SnapshotK13ChallengeInvariant, controlPendingSlots]
        at run ⊢
    all_goals subst next <;>
      simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
        controlExact] using invariant

def FutureFreeK13ChallengeInvariant (state : FutureFreeVerifierState) : Prop :=
  SnapshotK13ChallengeInvariant state.current ∧
    ∀ snapshot ∈ state.seen, SnapshotK13ChallengeInvariant snapshot

@[simp] theorem initial_future_free_k13_challenge_invariant
    (bindings : FixedBindings) :
    FutureFreeK13ChallengeInvariant
      (initialFutureFreeVerifierState bindings) := by
  simp [FutureFreeK13ChallengeInvariant, initialFutureFreeVerifierState,
    initial_snapshot_k13_challenge_invariant]

theorem append_future_free_snapshot_preserves_k13_challenge_invariant
    (state : FutureFreeVerifierState) (event : FutureFreeEvent)
    (next : FutureFreeSnapshot)
    (invariant : FutureFreeK13ChallengeInvariant state)
    (nextInvariant : SnapshotK13ChallengeInvariant next) :
    FutureFreeK13ChallengeInvariant
      (appendFutureFreeSnapshot state event next) := by
  constructor
  · exact nextInvariant
  · intro snapshot member
    simp only [appendFutureFreeSnapshot, List.mem_append,
      List.mem_singleton] at member
    rcases member with old | rfl
    · exact invariant.2 snapshot old
    · exact nextInvariant

theorem submit_next_raw_message_preserves_k13_challenge_invariant
    (raw : RawTag73ProverMessages) (state next : FutureFreeVerifierState)
    (invariant : FutureFreeK13ChallengeInvariant state)
    (submitted : submitNextRawMessage raw state = some next) :
    FutureFreeK13ChallengeInvariant next := by
  unfold submitNextRawMessage at submitted
  split at submitted
  next controlExact =>
    unfold submitFutureFreeC1 at submitted
    split at submitted
    next =>
      have nextExact := Option.some.inj submitted
      rw [← nextExact]
      apply append_future_free_snapshot_preserves_k13_challenge_invariant
        state _ _ invariant
      trivial
    all_goals simp at submitted
  next lambda chi controlExact =>
    have nextExact := Option.some.inj submitted
    rw [← nextExact]
    apply append_future_free_snapshot_preserves_k13_challenge_invariant
      state _ _ invariant
    trivial
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
        apply append_future_free_snapshot_preserves_k13_challenge_invariant
          state _ _ invariant
        have required : RequiredK13ChallengeRecords state.current remaining := by
          simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
            controlExact, RequiredK13ChallengeRecords, PendingOrRecorded] using
              invariant.1
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots] using
          (required_k13_challenge_records_transport
            (before := state.current) (after := { state.current with
              control := .absorbPayload (rawPayloadAt raw site) remaining
              receivedPayloads := state.current.receivedPayloads ++
                [rawPayloadAt raw site] }) rfl required)
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
      apply append_future_free_snapshot_preserves_k13_challenge_invariant
        state _ _ invariant
      have required : RequiredK13ChallengeRecords state.current remaining := by
        simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
          controlExact, RequiredK13ChallengeRecords, PendingOrRecorded] using
            invariant.1
      simpa [SnapshotK13ChallengeInvariant, controlPendingSlots] using
        (required_k13_challenge_records_transport
          (before := state.current) (after := { state.current with
            control := .workCheck stage (rawWorkNonceAt raw stage) remaining })
          rfl required)
    all_goals simp at submitted
  all_goals simp at submitted

theorem advance_future_free_verifier_preserves_k13_challenge_invariant
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (invariant : FutureFreeK13ChallengeInvariant state)
    (run : advanceFutureFreeVerifier environment state reply = some next) :
    FutureFreeK13ChallengeInvariant next := by
  rw [advanceFutureFreeVerifier] at run
  obtain ⟨action, _actionExact, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextCore, _coreExact, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextSnapshot, snapshotExact, finalExact⟩ :=
    Option.bind_eq_some_iff.mp run
  have nextSnapshotInvariant :=
    after_verifier_reply_preserves_snapshot_k13_challenges environment
      state.current nextSnapshot reply nextCore invariant.1 snapshotExact
  have nextExact := Option.some.inj finalExact
  subst next
  exact append_future_free_snapshot_preserves_k13_challenge_invariant
    state (.verifier action reply) nextSnapshot invariant nextSnapshotInvariant

theorem future_free_operational_step_preserves_k13_challenge_invariant
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (step : FutureFreeOperationalStep environment raw state pairs next)
    (invariant : FutureFreeK13ChallengeInvariant state) :
    FutureFreeK13ChallengeInvariant next := by
  cases step with
  | prover submitted event snapshot appendExact =>
      exact submit_next_raw_message_preserves_k13_challenge_invariant
        raw state next invariant submitted
  | verifier forced replyPath advanced =>
      exact advance_future_free_verifier_preserves_k13_challenge_invariant
        environment state next _ invariant advanced
  | stutter noSubmission noAction => exact invariant

theorem future_free_operational_trace_preserves_k13_challenge_invariant
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state final : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (trace : FutureFreeOperationalTrace environment raw state pairs final)
    (invariant : FutureFreeK13ChallengeInvariant state) :
    FutureFreeK13ChallengeInvariant final := by
  induction trace with
  | stop current => exact invariant
  | next step rest inductionHypothesis =>
      exact inductionHypothesis
        (future_free_operational_step_preserves_k13_challenge_invariant
          environment raw _ _ _ step invariant)

theorem restore_indexed_transition_preserves_k13_challenge_invariant
    (state : FutureFreeVerifierState) (transition : FutureFreeTransition)
    (invariant : FutureFreeK13ChallengeInvariant state)
    (closed : FutureFreeHistoryClosed state)
    (member : transition ∈ state.transitions) :
    FutureFreeK13ChallengeInvariant (restoreIndexedTransition transition) := by
  have beforeSeen : transition.before ∈ state.seen :=
    (closed.2.2 transition member).1
  have beforeInvariant := invariant.2 transition.before beforeSeen
  exact ⟨beforeInvariant, by
    intro snapshot seen
    simp [restoreIndexedTransition] at seen
    subst snapshot
    exact beforeInvariant⟩

/-- A completed verifier necessarily exposes exact verifier-owned gamma and
alpha-zero records. -/
theorem done_state_has_exact_gamma_alpha_zero
    (state : FutureFreeVerifierState)
    (invariant : FutureFreeK13ChallengeInvariant state)
    (done : state.current.control = .done) :
    ExactRecordedChallenge state.current .gamma ∧
      ExactRecordedChallenge state.current (.alpha 0) := by
  simpa [SnapshotK13ChallengeInvariant, controlPendingSlots,
    RequiredK13ChallengeRecords, PendingOrRecorded, done] using invariant.1

#print axioms initial_snapshot_k13_challenge_invariant
#print axioms process_challenge_block_preserves_k13_challenge_invariant
#print axioms after_verifier_reply_preserves_snapshot_k13_challenges
#print axioms submit_next_raw_message_preserves_k13_challenge_invariant
#print axioms advance_future_free_verifier_preserves_k13_challenge_invariant
#print axioms future_free_operational_trace_preserves_k13_challenge_invariant
#print axioms restore_indexed_transition_preserves_k13_challenge_invariant
#print axioms done_state_has_exact_gamma_alpha_zero

end

end AspisK1.V7Tag73ChallengeRecordControlInvariant
