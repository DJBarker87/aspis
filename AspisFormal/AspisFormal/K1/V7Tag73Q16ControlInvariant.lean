import AspisFormal.K1.V7Tag73RawFutureFreeDriver

/-!
# Reachable q16 controls have an exact pre-answer digest slot

The future-free controller stores a q16 candidate counter and the output
blocks already consumed for that candidate.  The bare `FutureFreeControl`
type permits an arbitrary list, but the executable controller never reaches
`q16Sample` with eight or more blocks: after the eighth unsuccessful decoder
attempt it rejects instead of requesting another squeeze.

This file proves that operational reachability invariant for the current
state and every snapshot retained in its restoration history.  Consequently
an actual restored q16 squeeze names a literal `Fin 64 × Fin 8` slot before
the next SHA answer is exposed.  No acceptance, probability, decoder-success,
or extraction premise appears here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73Q16ControlInvariant

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver

noncomputable section

/-- Local well-formedness of the incremental q16 controller. -/
def Q16ControlSlotBound : FutureFreeControl → Prop
  | .q16Sample _base _counter outputs _remaining => outputs.length < 8
  | _ => True

def Q16SnapshotSlotBound (snapshot : FutureFreeSnapshot) : Prop :=
  Q16ControlSlotBound snapshot.control

@[simp] theorem linear_or_done_q16_control_slot_bound
    (remaining : List FutureFreeSlot) :
    Q16ControlSlotBound (linearOrDone remaining) := by
  cases remaining <;> trivial

/-- The live snapshot and every complete restoration target retained by the
driver have a valid q16 block index. -/
def FutureFreeQ16SlotInvariant (state : FutureFreeVerifierState) : Prop :=
  Q16SnapshotSlotBound state.current ∧
    ∀ snapshot ∈ state.seen, Q16SnapshotSlotBound snapshot

@[simp] theorem initial_future_free_q16_slot_invariant
    (bindings : FixedBindings) :
    FutureFreeQ16SlotInvariant (initialFutureFreeVerifierState bindings) := by
  simp [FutureFreeQ16SlotInvariant, Q16SnapshotSlotBound,
    Q16ControlSlotBound, initialFutureFreeVerifierState,
    initialFutureFreeSnapshot]

theorem append_future_free_snapshot_preserves_q16_slot_invariant
    (state : FutureFreeVerifierState) (event : FutureFreeEvent)
    (next : FutureFreeSnapshot)
    (invariant : FutureFreeQ16SlotInvariant state)
    (nextBound : Q16SnapshotSlotBound next) :
    FutureFreeQ16SlotInvariant (appendFutureFreeSnapshot state event next) := by
  constructor
  · exact nextBound
  · intro snapshot member
    simp only [appendFutureFreeSnapshot, List.mem_append,
      List.mem_singleton] at member
    rcases member with old | rfl
    · exact invariant.2 snapshot old
    · exact nextBound

/-- A prover submission cannot create or enlarge a q16 sampler state. -/
private theorem submit_future_free_c1_current_q16_slot_bound
    (state next : FutureFreeVerifierState)
    (root : TypedMerkleRoot .initialC1)
    (submitted : submitFutureFreeC1 state root = some next) :
    Q16SnapshotSlotBound next.current := by
  unfold submitFutureFreeC1 at submitted
  split at submitted
  next controlExact =>
    have nextExact := Option.some.inj submitted
    rw [← nextExact]
    simp [appendFutureFreeSnapshot, Q16SnapshotSlotBound,
      Q16ControlSlotBound]
  all_goals simp at submitted

private theorem submit_future_free_c2_current_q16_slot_bound
    (state next : FutureFreeVerifierState)
    (lambda chi : Qm31Bytes) (commitment : C2Commitment lambda chi)
    (atC2 : state.current.control = .adaptive (.awaitingC2 lambda chi))
    (submitted : submitFutureFreeC2 state lambda chi commitment atC2 = next) :
    Q16SnapshotSlotBound next.current := by
  rw [← submitted]
  simp [submitFutureFreeC2, appendFutureFreeSnapshot,
    Q16SnapshotSlotBound, Q16ControlSlotBound]

private theorem submit_future_free_payload_current_q16_slot_bound
    (state next : FutureFreeVerifierState) (payload : Payload)
    (submitted : submitFutureFreePayload state payload = some next) :
    Q16SnapshotSlotBound next.current := by
  unfold submitFutureFreePayload at submitted
  split at submitted
  next site remaining controlExact =>
    split at submitted
    next matched =>
      have nextExact := Option.some.inj submitted
      rw [← nextExact]
      simp [appendFutureFreeSnapshot, Q16SnapshotSlotBound,
        Q16ControlSlotBound]
    next => simp at submitted
  all_goals simp at submitted

private theorem submit_future_free_work_current_q16_slot_bound
    (state next : FutureFreeVerifierState) (nonce : NonceBytes)
    (submitted : submitFutureFreeWorkNonce state nonce = some next) :
    Q16SnapshotSlotBound next.current := by
  unfold submitFutureFreeWorkNonce at submitted
  split at submitted
  next stage remaining controlExact =>
    have nextExact := Option.some.inj submitted
    rw [← nextExact]
    simp [appendFutureFreeSnapshot, Q16SnapshotSlotBound,
      Q16ControlSlotBound]
  all_goals simp at submitted

theorem submit_next_raw_message_preserves_current_q16_slot_bound
    (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (submitted : submitNextRawMessage raw state = some next) :
    Q16SnapshotSlotBound next.current := by
  unfold submitNextRawMessage at submitted
  split at submitted
  next controlExact =>
    exact submit_future_free_c1_current_q16_slot_bound state next
      (rawC1Root raw) submitted
  next lambda chi controlExact =>
    have nextExact :
        submitFutureFreeC2 state lambda chi (raw.c2Commitment lambda chi)
          controlExact = next := Option.some.inj submitted
    exact submit_future_free_c2_current_q16_slot_bound state next lambda chi
      (raw.c2Commitment lambda chi) controlExact nextExact
  next site remaining controlExact =>
    exact submit_future_free_payload_current_q16_slot_bound state next
      (rawPayloadAt raw site) submitted
  next stage remaining controlExact =>
    exact submit_future_free_work_current_q16_slot_bound state next
      (rawWorkNonceAt raw stage) submitted
  all_goals simp at submitted

theorem submit_next_raw_message_preserves_q16_slot_invariant
    (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (invariant : FutureFreeQ16SlotInvariant state)
    (submitted : submitNextRawMessage raw state = some next) :
    FutureFreeQ16SlotInvariant next := by
  obtain ⟨event, snapshot, nextExact⟩ :=
    successful_raw_submission_is_complete_append raw state next submitted
  rw [nextExact]
  apply append_future_free_snapshot_preserves_q16_slot_invariant state event
    snapshot invariant
  have currentBound :=
    submit_next_raw_message_preserves_current_q16_slot_bound raw state next
      submitted
  simpa [nextExact, appendFutureFreeSnapshot] using currentBound

/-- Challenge sampling never enters the q16 controller. -/
@[simp] private theorem complete_future_free_challenge_q16_slot_bound
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (value : Qm31Bytes)
    (remaining : List FutureFreeSlot) (nextCore : RuntimeCore) :
    Q16SnapshotSlotBound
      (completeFutureFreeChallenge environment snapshot id value remaining
        nextCore) := by
  cases id <;> cases remaining <;>
    simp [completeFutureFreeChallenge, Q16SnapshotSlotBound,
      Q16ControlSlotBound, linearOrDone]
  all_goals
    cases decoded : environment.decoders.secureCirclePoint value <;>
      simp [decoded, Q16SnapshotSlotBound, Q16ControlSlotBound, linearOrDone]

@[simp] private theorem process_future_free_challenge_block_q16_slot_bound
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) :
    Q16SnapshotSlotBound
      (processFutureFreeChallengeBlock environment snapshot id outputs
        remaining output nextCore) := by
  cases decoded : environment.decoders.qm31Parameter id
      (outputs ++ [output]) with
  | some value =>
      simp [processFutureFreeChallengeBlock, decoded]
  | none =>
      by_cases belowCap :
          (outputs ++ [output]).length < samplerBlockCap (samplerMode id)
      · have belowCap' :
            outputs.length + 1 < samplerBlockCap (samplerMode id) := by
          simpa using belowCap
        simp [processFutureFreeChallengeBlock, decoded, belowCap',
          Q16SnapshotSlotBound, Q16ControlSlotBound]
      · have belowCap' :
            ¬ outputs.length + 1 < samplerBlockCap (samplerMode id) := by
          simpa using belowCap
        simp [processFutureFreeChallengeBlock, decoded, belowCap',
          Q16SnapshotSlotBound, Q16ControlSlotBound]

/-- Candidate processing requests another block only under the literal
strict cap test. -/
@[simp] private theorem process_future_free_candidate_block_q16_slot_bound
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) :
    Q16SnapshotSlotBound
      (processFutureFreeCandidateBlock environment snapshot base counter
        outputs remaining output nextCore) := by
  cases decoded : environment.decoders.candidate counter
      (outputs ++ [output]) with
  | none =>
      by_cases belowCap : (outputs ++ [output]).length < 8
      · have belowCap' : outputs.length + 1 < 8 := by simpa using belowCap
        simp [processFutureFreeCandidateBlock, decoded, belowCap',
          Q16SnapshotSlotBound, Q16ControlSlotBound]
      · have belowCap' : ¬ outputs.length + 1 < 8 := by simpa using belowCap
        simp [processFutureFreeCandidateBlock, decoded, belowCap',
          Q16SnapshotSlotBound, Q16ControlSlotBound]
  | some outcome =>
      cases outcome with
      | samplerAbort =>
          simp [processFutureFreeCandidateBlock, decoded,
            Q16SnapshotSlotBound, Q16ControlSlotBound]
      | schedule schedule =>
          by_cases compact : environment.frontierNodes schedule ≤ 203
          · simp [processFutureFreeCandidateBlock, decoded, compact,
              Q16SnapshotSlotBound, Q16ControlSlotBound]
          · simp [processFutureFreeCandidateBlock, decoded, compact,
              Q16SnapshotSlotBound, Q16ControlSlotBound]

/-- The raw controller update preserves the local cap. -/
private theorem raw_after_future_free_verifier_reply_preserves_q16_slot_bound
    (environment : FutureFreeEnvironment)
    (snapshot next : FutureFreeSnapshot)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (currentBound : Q16SnapshotSlotBound snapshot)
    (advanced : rawAfterFutureFreeVerifierReply environment snapshot reply
      nextCore = some next) :
    Q16SnapshotSlotBound next := by
  cases controlExact : snapshot.control with
  | adaptive control =>
      cases reply <;>
        simp only [rawAfterFutureFreeVerifierReply, controlExact] at advanced
      all_goals
        obtain ⟨nextAdaptive, _adaptiveExact, nextExact⟩ :=
          Option.bind_eq_some_iff.mp advanced
        rw [← Option.some.inj nextExact]
        cases nextAdaptive <;>
          simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | linear remaining =>
      cases remaining with
      | nil =>
          cases reply <;>
            simp_all [rawAfterFutureFreeVerifierReply]
      | cons slot rest =>
          cases slot <;> cases reply <;>
            simp_all [rawAfterFutureFreeVerifierReply,
              Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
            subst_vars <;>
            first
            | exact linear_or_done_q16_control_slot_bound _
            | exact process_future_free_challenge_block_q16_slot_bound
                environment snapshot _ _ _ _ nextCore
            | simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | absorbPayload payload remaining =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;>
        exact linear_or_done_q16_control_slot_bound _
  | workCheck stage nonce remaining =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;> simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | workCheckpoint stage nonce remaining =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;> simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | workAbsorb stage nonce remaining =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;>
        exact linear_or_done_q16_control_slot_bound _
  | sampleChallenge id outputs remaining =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;>
        first
        | exact process_future_free_challenge_block_q16_slot_bound
            environment snapshot _ _ _ _ nextCore
        | simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | q16Absorb base counter remaining =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;> simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | q16Sample base counter outputs remaining =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;>
        first
        | exact process_future_free_candidate_block_q16_slot_bound
            environment snapshot _ _ _ _ _ nextCore
        | simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | q16Restore base counter nextCounter remaining =>
      cases nextCounter <;> cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;> simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | q16Selected base counter schedule remaining =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;>
        exact linear_or_done_q16_control_slot_bound _
  | q16SamplerReject counter reason =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;> simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | q16AllNoncompactReject =>
      cases reply <;>
        simp_all [rawAfterFutureFreeVerifierReply,
          Q16SnapshotSlotBound, Q16ControlSlotBound] <;>
        subst_vars <;> simp [Q16SnapshotSlotBound, Q16ControlSlotBound]
  | rejected reason =>
      cases reply <;> simp_all [rawAfterFutureFreeVerifierReply]
  | done =>
      cases reply <;> simp_all [rawAfterFutureFreeVerifierReply]

/-- One successful verifier reply preserves the local q16 block cap.  The
only nontrivial branch is an undecoded candidate block: the executable test
`accumulated.length < 8` is exactly the premise under which the controller
requests the next block. -/
theorem after_future_free_verifier_reply_preserves_q16_slot_bound
    (environment : FutureFreeEnvironment)
    (snapshot next : FutureFreeSnapshot)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (currentBound : Q16SnapshotSlotBound snapshot)
    (advanced : afterFutureFreeVerifierReply environment snapshot reply
      nextCore = some next) :
    Q16SnapshotSlotBound next := by
  unfold afterFutureFreeVerifierReply at advanced
  cases rawExact : rawAfterFutureFreeVerifierReply environment snapshot reply
      nextCore with
  | none => simp [rawExact] at advanced
  | some candidate =>
      rw [rawExact] at advanced
      have nextExact : { candidate with bindings := snapshot.bindings } = next :=
        Option.some.inj advanced
      rw [← nextExact]
      simpa [Q16SnapshotSlotBound] using
        (raw_after_future_free_verifier_reply_preserves_q16_slot_bound
          environment snapshot candidate reply nextCore currentBound rawExact)

theorem advance_future_free_verifier_preserves_q16_slot_invariant
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (invariant : FutureFreeQ16SlotInvariant state)
    (advanced : advanceFutureFreeVerifier environment state reply = some next) :
    FutureFreeQ16SlotInvariant next := by
  rw [advanceFutureFreeVerifier] at advanced
  obtain ⟨action, _actionExact, advanced⟩ :=
    Option.bind_eq_some_iff.mp advanced
  obtain ⟨nextCore, _coreExact, advanced⟩ :=
    Option.bind_eq_some_iff.mp advanced
  obtain ⟨nextSnapshot, snapshotExact, finalExact⟩ :=
    Option.bind_eq_some_iff.mp advanced
  have nextBound :=
    after_future_free_verifier_reply_preserves_q16_slot_bound environment
      state.current nextSnapshot reply nextCore invariant.1 snapshotExact
  have nextExact :
      appendFutureFreeSnapshot state (.verifier action reply) nextSnapshot =
        next := Option.some.inj finalExact
  rw [← nextExact]
  exact append_future_free_snapshot_preserves_q16_slot_invariant state
    (.verifier action reply) nextSnapshot invariant nextBound

/-- Every chronological operational trace preserves the cap, including all
snapshots retained for later state restoration. -/
theorem future_free_operational_trace_preserves_q16_slot_invariant
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    ∀ {initial pairs final},
      FutureFreeOperationalTrace environment raw initial pairs final →
      FutureFreeQ16SlotInvariant initial →
      FutureFreeQ16SlotInvariant final := by
  intro initial pairs final trace
  induction trace with
  | stop state => intro invariant; exact invariant
  | @next state middle final head tail step rest ih =>
      intro invariant
      apply ih
      cases step with
      | prover submitted event snapshot appendExact =>
          exact submit_next_raw_message_preserves_q16_slot_invariant raw state
            middle invariant submitted
      | verifier forced replyPath advanced =>
          exact advance_future_free_verifier_preserves_q16_slot_invariant
            environment state middle _ invariant advanced
      | stutter noSubmission noAction =>
          exact invariant

/-- An actually retained q16 sampler snapshot supplies its literal finite
digest slot without any decoder or acceptance assumption. -/
def q16DigestSlotOfBoundedSnapshot
    (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot)
    (controlExact : snapshot.control =
      .q16Sample base counter outputs remaining)
    (bounded : Q16SnapshotSlotBound snapshot) : Fin 64 × Fin 8 :=
  (counter, ⟨outputs.length, by
    rw [Q16SnapshotSlotBound, controlExact] at bounded
    exact bounded⟩)

@[simp] theorem q16_digest_slot_of_bounded_snapshot_counter
    (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot)
    (controlExact : snapshot.control =
      .q16Sample base counter outputs remaining)
    (bounded : Q16SnapshotSlotBound snapshot) :
    (q16DigestSlotOfBoundedSnapshot snapshot base counter outputs remaining
      controlExact bounded).1 = counter := by
  rfl

@[simp] theorem q16_digest_slot_of_bounded_snapshot_block
    (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot)
    (controlExact : snapshot.control =
      .q16Sample base counter outputs remaining)
    (bounded : Q16SnapshotSlotBound snapshot) :
    (q16DigestSlotOfBoundedSnapshot snapshot base counter outputs remaining
      controlExact bounded).2.val = outputs.length := by
  rfl

#print axioms initial_future_free_q16_slot_invariant
#print axioms submit_next_raw_message_preserves_q16_slot_invariant
#print axioms after_future_free_verifier_reply_preserves_q16_slot_bound
#print axioms advance_future_free_verifier_preserves_q16_slot_invariant
#print axioms future_free_operational_trace_preserves_q16_slot_invariant
#print axioms q16DigestSlotOfBoundedSnapshot

end

end AspisK1.V7Tag73Q16ControlInvariant
