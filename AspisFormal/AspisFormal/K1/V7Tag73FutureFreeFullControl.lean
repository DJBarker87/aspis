import AspisFormal.K1.V7Tag73ResumeDerivedReplayNode
import AspisFormal.K1.V7Tag73SecureCircleMap
import AspisFormal.K1.V7Tag73IncrementalSamplerControl

/-!
# A future-free full Tag-73 verifier controller

This module extends the future-free adaptive C1/lambda/chi/C2 fragment through
the remaining deployed Tag-73 schedule.  The controller stores no
`DeployedFixedTape` and accepts no caller-selected verifier action.  Its next
action is a function of its current control state.

The concrete sampler and circle decoder is fixed to
`exactDeterministicDecoders`.  Challenge values, secure circle points, and q16
candidate outcomes are recomputed from paired verifier replies.  They are not
trusted fields of a replayed proof.  The q16 controller saves one actual base,
visits counters in order, runs each candidate incrementally for at most eight
blocks, restores only through the protocol-specific `q16Restore` action, and
continues only from the first schedule whose exact frontier has at most 203
nodes.

Exploratory grinding probes are deliberately absent: they are adversary query
history, not messages of the ROM-free verifier.  At each of the batch, fold,
and final sites the prover submits one selected nonce.  The knowledge
ancestor retains its one selected-nonce query, stage checkpoint, and exact
nonce absorb while erasing only the leading-zero predicate.  A separate
strict-to-erased theorem below proves the deployed strict run maps to this
ancestor.

This is an operational verifier controller.  It does not claim the still
missing source/replay suffix-splice theorem, fixed-tape bisimulation, or any
probability/extraction conclusion.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FutureFreeFullControl

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73SamplerDecoder

noncomputable section

/-! ## Future-free schedule grammar -/

inductive FutureFreePayloadSite where
  | initialMaskClaim
  | semanticRound (round : Fin 10)
  | pointClaims
  | inactiveClaim
  | circleOodValue (sample : Fin 2)
  | relationRound (round : Fin 4)
  | final256
  | queryBatchClaim
  deriving DecidableEq, Repr

def payloadMatchesSite : FutureFreePayloadSite → Payload → Bool
  | .initialMaskClaim, .initialMaskClaim _ => true
  | .semanticRound expected, .semanticRound actual _ => actual == expected
  | .pointClaims, .pointClaims _ => true
  | .inactiveClaim, .inactiveClaim _ => true
  | .circleOodValue expected, .circleOodValue actual _ => actual == expected
  | .relationRound expected, .relationRound actual _ => actual == expected
  | .final256, .final256 _ => true
  | .queryBatchClaim, .queryBatchClaim _ => true
  | _, _ => false

inductive FutureFreeSlot where
  | fixed (action : VerifierAction)
  | challenge (id : ChallengeId)
  | payload (site : FutureFreePayloadSite)
  | work (stage : WorkStage)
  | beginQ16

def zeroCheckSlots : List FutureFreeSlot :=
  List.ofFn fun coordinate : Fin 10 =>
    .challenge (.zerocheckPoint coordinate)

def semanticSlots : List FutureFreeSlot :=
  (List.ofFn fun round : Fin 10 =>
    [.payload (.semanticRound round),
     .challenge (.semantic round)]).flatten

def oodSlots : List FutureFreeSlot :=
  (List.ofFn fun sample : Fin 2 =>
    [.challenge (.circlePoint sample),
     .payload (.circleOodValue sample),
     .challenge (.oodMix sample)]).flatten

def relationTailSlots : List FutureFreeSlot :=
  (List.ofFn fun tail : Fin 3 =>
    let round : Fin 4 := ⟨tail.val + 1, by omega⟩
    [.payload (.relationRound round),
     .challenge (.alpha round)]).flatten

def beforeQ16Slots : List FutureFreeSlot :=
  [.fixed (.absorb .constraintRegistry),
   .fixed (.absorb .helperSum),
   .challenge .theta] ++
  zeroCheckSlots ++
  [.challenge .mu,
   .payload .initialMaskClaim,
   .challenge .eta] ++
  semanticSlots ++
  [.payload .pointClaims,
   .fixed (.checkpoint .semanticTerminal),
   .work .batch,
   .challenge .gamma,
   .payload .inactiveClaim,
   .challenge .kappa] ++
  oodSlots ++
  [.payload (.relationRound 0),
   .work .fold,
   .challenge (.alpha 0),
   .payload .final256,
   .work .final]

def afterQ16Slots : List FutureFreeSlot :=
  [.fixed (.checkpoint .frontierCount),
   .fixed (.absorb .queryBatchDomain),
   .challenge .queryBatch,
   .fixed (.checkpoint .twoTreeAuthentication),
   .payload .queryBatchClaim] ++
  relationTailSlots ++
  [.fixed (.checkpoint .relationTerminal), .fixed .terminal]

def fullFutureFreeSlots : List FutureFreeSlot :=
  beforeQ16Slots ++ [.beginQ16] ++ afterQ16Slots

def workStagesInSlots : List FutureFreeSlot → List WorkStage
  | [] => []
  | .work stage :: rest => stage :: workStagesInSlots rest
  | _ :: rest => workStagesInSlots rest

theorem work_stages_are_exactly_batch_fold_final :
    workStagesInSlots fullFutureFreeSlots = [.batch, .fold, .final] := by
  rfl

theorem semantic_slots_have_exact_round_pairs :
    semanticSlots =
      (List.ofFn fun round : Fin 10 =>
        [FutureFreeSlot.payload (.semanticRound round),
         FutureFreeSlot.challenge (.semantic round)]).flatten := by
  rfl

theorem ood_slots_have_exact_circle_value_mix_triples :
    oodSlots =
      (List.ofFn fun sample : Fin 2 =>
        [FutureFreeSlot.challenge (.circlePoint sample),
         FutureFreeSlot.payload (.circleOodValue sample),
         FutureFreeSlot.challenge (.oodMix sample)]).flatten := by
  rfl

/-! ## Live accumulated semantic state -/

structure DecodedChallenge where
  id : ChallengeId
  value : Qm31Bytes

structure DecodedCirclePoint where
  sample : Fin 2
  parameter : Qm31Bytes
  point : SecureCirclePointBytes

structure CheckedWorkNonce where
  stage : WorkStage
  nonce : NonceBytes

structure DecodedQ16Candidate where
  counter : Fin 64
  outcome : CandidateOutcome

/-- `frontierNodes` is the exact topology function supplied by the K1.2
query-graph layer.  This module never replaces it by a size slogan or a
caller-supplied selected result; the controller evaluates it on every decoded
candidate schedule. -/
structure FutureFreeEnvironment where
  frontierNodes : QuerySchedule → Nat

def FutureFreeEnvironment.decoders
    (_environment : FutureFreeEnvironment) : DeterministicDecoders :=
  exactDeterministicDecoders

inductive FutureFreeRejectReason where
  | challengeSamplerCap (id : ChallengeId)
  | secureCirclePoint (sample : Fin 2)
  | q16SamplerAbort (counter : Fin 64)
  | q16DecoderCap (counter : Fin 64)
  | q16AllNoncompact
  deriving DecidableEq, Repr

def nextQ16Counter? (counter : Fin 64) : Option (Fin 64) :=
  if available : counter.val + 1 < 64 then
    some ⟨counter.val + 1, available⟩
  else
    none

inductive FutureFreeControl where
  | adaptive (control : OpenAdaptiveControl)
  | linear (remaining : List FutureFreeSlot)
  | absorbPayload (payload : Payload) (remaining : List FutureFreeSlot)
  | workCheck (stage : WorkStage) (nonce : NonceBytes)
      (remaining : List FutureFreeSlot)
  | workCheckpoint (stage : WorkStage) (nonce : NonceBytes)
      (remaining : List FutureFreeSlot)
  | workAbsorb (stage : WorkStage) (nonce : NonceBytes)
      (remaining : List FutureFreeSlot)
  | sampleChallenge (id : ChallengeId) (outputs : List Digest256)
      (remaining : List FutureFreeSlot)
  | q16Absorb (base : Digest256) (counter : Fin 64)
      (remaining : List FutureFreeSlot)
  | q16Sample (base : Digest256) (counter : Fin 64)
      (outputs : List Digest256) (remaining : List FutureFreeSlot)
  | q16Restore (base : Digest256) (counter : Fin 64)
      (nextCounter : Option (Fin 64)) (remaining : List FutureFreeSlot)
  | q16Selected (base : Digest256) (counter : Fin 64)
      (schedule : QuerySchedule) (remaining : List FutureFreeSlot)
  | q16SamplerReject (counter : Fin 64) (reason : FutureFreeRejectReason)
  | q16AllNoncompactReject
  | rejected (reason : FutureFreeRejectReason)
  | done

def linearOrDone : List FutureFreeSlot → FutureFreeControl
  | [] => .done
  | remaining => .linear remaining

def checkpointOfWorkStage : WorkStage → Checkpoint
  | .batch => .batchWork
  | .fold => .foldWork
  | .final => .finalWork

def workNoncePayload : (stage : WorkStage) → NonceBytes → Payload
  | .batch => .batchNonce
  | .fold => .foldNonce
  | .final => .finalNonce

def FutureFreeControl.nextVerifierAction? :
    FutureFreeControl → Option VerifierAction
  | .adaptive control => control.nextVerifierAction?
  | .linear [] => none
  | .linear (.fixed action :: _) => some action
  | .linear (.challenge id :: _) =>
      some (.squeezePair (.challenge id) 0)
  | .linear (.beginQ16 :: _) => some .markQ16Base
  | .linear (.payload _ :: _) => none
  | .linear (.work _ :: _) => none
  | .absorbPayload payload _ => some (.absorb payload)
  | .workCheck stage nonce _ =>
      some (.workProbe stage nonce .verifierSelected)
  | .workCheckpoint stage _ _ =>
      some (.checkpoint (checkpointOfWorkStage stage))
  | .workAbsorb stage nonce _ => some (.absorb (workNoncePayload stage nonce))
  | .sampleChallenge id outputs _ =>
      some (.squeezePair (.challenge id) outputs.length)
  | .q16Absorb _ counter _ => some (.absorb (.queryCandidate counter))
  | .q16Sample _ counter outputs _ =>
      some (.squeezePair (.queryCandidate counter) outputs.length)
  | .q16Restore _ counter _ _ => some (.q16Restore counter)
  | .q16Selected _ counter _ _ => some (.q16Selected counter)
  | .q16SamplerReject counter _ => some (.q16SamplerAbortReject counter)
  | .q16AllNoncompactReject => some .q16AllNoncompactReject
  | .rejected _ => none
  | .done => none

structure FutureFreeSnapshot where
  control : FutureFreeControl
  bindings : FixedBindings
  core : RuntimeCore
  c1Root : Option Digest208
  c2Root : Option Digest208
  decodedChallenges : List DecodedChallenge
  circlePoints : List DecodedCirclePoint
  receivedPayloads : List Payload
  checkedWorkNonces : List CheckedWorkNonce
  q16Candidates : List DecodedQ16Candidate

inductive FutureFreeEvent where
  | proverC1 (root : TypedMerkleRoot .initialC1)
  | proverC2 (lambda chi : Qm31Bytes)
      (commitment : C2Commitment lambda chi)
  | proverPayload (payload : Payload)
  | proverWorkNonce (stage : WorkStage) (nonce : NonceBytes)
  | verifier (action : VerifierAction) (reply : VerifierReply)

structure FutureFreeTransition where
  before : FutureFreeSnapshot
  event : FutureFreeEvent
  after : FutureFreeSnapshot

structure FutureFreeVerifierState where
  current : FutureFreeSnapshot
  seen : List FutureFreeSnapshot
  transitions : List FutureFreeTransition

def initialFutureFreeSnapshot (bindings : FixedBindings) : FutureFreeSnapshot :=
  { control := .adaptive
      (.fixedPrefix (openFixedPrefixActions bindings))
    bindings := bindings
    core := initialCore
    c1Root := none
    c2Root := none
    decodedChallenges := []
    circlePoints := []
    receivedPayloads := []
    checkedWorkNonces := []
    q16Candidates := [] }

def initialFutureFreeVerifierState (bindings : FixedBindings) :
    FutureFreeVerifierState :=
  let current := initialFutureFreeSnapshot bindings
  { current := current, seen := [current], transitions := [] }

def appendFutureFreeSnapshot (state : FutureFreeVerifierState)
    (event : FutureFreeEvent) (next : FutureFreeSnapshot) :
    FutureFreeVerifierState :=
  { current := next
    seen := state.seen ++ [next]
    transitions := state.transitions ++
      [{ before := state.current, event := event, after := next }] }

@[simp] theorem initial_future_free_history_is_nonempty
    (bindings : FixedBindings) :
    (initialFutureFreeVerifierState bindings).seen ≠ [] := by
  simp [initialFutureFreeVerifierState]

/-! ## Executable prover submissions -/

def submitFutureFreeC1 (state : FutureFreeVerifierState)
    (root : TypedMerkleRoot .initialC1) :
    Option FutureFreeVerifierState :=
  match state.current.control with
  | .adaptive .awaitingC1 =>
      let next : FutureFreeSnapshot :=
        { state.current with
          control := .adaptive (.requestC1Salt root)
          c1Root := some root.value }
      some (appendFutureFreeSnapshot state (.proverC1 root) next)
  | _ => none

def submitFutureFreeC2 (state : FutureFreeVerifierState)
    (lambda chi : Qm31Bytes) (commitment : C2Commitment lambda chi)
    (_atC2 : state.current.control =
      .adaptive (.awaitingC2 lambda chi)) : FutureFreeVerifierState :=
  let next : FutureFreeSnapshot :=
    { state.current with
      control := .adaptive (.requestC2Salt lambda chi commitment)
      c2Root := some commitment.root }
  appendFutureFreeSnapshot state (.proverC2 lambda chi commitment) next

def submitFutureFreePayload (state : FutureFreeVerifierState)
    (payload : Payload) : Option FutureFreeVerifierState :=
  match state.current.control with
  | .linear (.payload site :: remaining) =>
      if payloadMatchesSite site payload then
        let next : FutureFreeSnapshot :=
          { state.current with
            control := .absorbPayload payload remaining
            receivedPayloads := state.current.receivedPayloads ++ [payload] }
        some (appendFutureFreeSnapshot state (.proverPayload payload) next)
      else
        none
  | _ => none

def submitFutureFreeWorkNonce (state : FutureFreeVerifierState)
    (nonce : NonceBytes) : Option FutureFreeVerifierState :=
  match state.current.control with
  | .linear (.work stage :: remaining) =>
      let next : FutureFreeSnapshot :=
        { state.current with
          control := .workCheck stage nonce remaining }
      some (appendFutureFreeSnapshot state (.proverWorkNonce stage nonce) next)
  | _ => none

theorem submitted_c2_is_indexed_by_current_decoded_values
    (state : FutureFreeVerifierState) (lambda chi : Qm31Bytes)
    (commitment : C2Commitment lambda chi)
    (atC2 : state.current.control =
      .adaptive (.awaitingC2 lambda chi)) :
    (submitFutureFreeC2 state lambda chi commitment atC2).current.control =
        .adaptive (.requestC2Salt lambda chi commitment) ∧
      (submitFutureFreeC2 state lambda chi commitment atC2).current.c2Root =
        some commitment.root := by
  exact ⟨rfl, rfl⟩

theorem submitted_work_nonce_has_only_one_selected_check
    (stage : WorkStage) (nonce : NonceBytes)
    (remaining : List FutureFreeSlot) :
    FutureFreeControl.nextVerifierAction?
        (.workCheck stage nonce remaining) =
      some (.workProbe stage nonce .verifierSelected) := by
  rfl

/-! ## Deterministic challenge and q16 updates -/

def completeFutureFreeChallenge (environment : FutureFreeEnvironment)
    (snapshot : FutureFreeSnapshot) (id : ChallengeId)
    (value : Qm31Bytes) (remaining : List FutureFreeSlot)
    (nextCore : RuntimeCore) : FutureFreeSnapshot :=
  let decoded := snapshot.decodedChallenges ++ [{ id := id, value := value }]
  match id with
  | .circlePoint sample =>
      match environment.decoders.secureCirclePoint value with
      | none =>
          { snapshot with
            control := .rejected (.secureCirclePoint sample)
            core := nextCore
            decodedChallenges := decoded }
      | some point =>
          { snapshot with
            control := linearOrDone remaining
            core := nextCore
            decodedChallenges := decoded
            circlePoints := snapshot.circlePoints ++
              [{ sample := sample, parameter := value, point := point }] }
  | _ =>
      { snapshot with
        control := linearOrDone remaining
        core := nextCore
        decodedChallenges := decoded }

def processFutureFreeChallengeBlock
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) : FutureFreeSnapshot :=
  let accumulated := outputs ++ [output]
  match environment.decoders.qm31Parameter id accumulated with
  | some value =>
      completeFutureFreeChallenge environment snapshot id value remaining
        nextCore
  | none =>
      if accumulated.length < samplerBlockCap (samplerMode id) then
        { snapshot with
          control := .sampleChallenge id accumulated remaining
          core := nextCore }
      else
        { snapshot with
          control := .rejected (.challengeSamplerCap id)
          core := nextCore }

def processFutureFreeCandidateBlock
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) : FutureFreeSnapshot :=
  let accumulated := outputs ++ [output]
  match environment.decoders.candidate counter accumulated with
  | some .samplerAbort =>
      { snapshot with
        control := .q16SamplerReject counter (.q16SamplerAbort counter)
        core := nextCore
        q16Candidates := snapshot.q16Candidates ++
          [{ counter := counter, outcome := .samplerAbort }] }
  | some (.schedule schedule) =>
      let recorded := snapshot.q16Candidates ++
        [{ counter := counter, outcome := .schedule schedule }]
      if environment.frontierNodes schedule ≤ 203 then
        { snapshot with
          control := .q16Selected base counter schedule remaining
          core := nextCore
          q16Candidates := recorded }
      else
        { snapshot with
          control := .q16Restore base counter (nextQ16Counter? counter)
            remaining
          core := nextCore
          q16Candidates := recorded }
  | none =>
      if accumulated.length < 8 then
        { snapshot with
          control := .q16Sample base counter accumulated remaining
          core := nextCore }
      else
        { snapshot with
          control := .q16SamplerReject counter (.q16DecoderCap counter)
          core := nextCore }

/-! ## Exact incremental-sampler and first-compact facts -/

theorem accepted_future_free_challenge_is_prefix_minimal
    (environment : FutureFreeEnvironment) (id : ChallengeId)
    (blocks : List Digest256) (value : Qm31Bytes)
    (accepted : environment.decoders.qm31Parameter id blocks = some value) :
    ∀ count, count < blocks.length →
      environment.decoders.qm31Parameter id (blocks.take count) = none := by
  change decodeChallengeParameter exactSecureCircleParameterMap id blocks =
    some value at accepted
  intro count strict
  change decodeChallengeParameter exactSecureCircleParameterMap id
    (blocks.take count) = none
  exact decodeChallengeParameter_accepted_is_prefix_minimal
    exactSecureCircleParameterMap id blocks value accepted count strict

theorem accepted_future_free_candidate_is_prefix_minimal
    (environment : FutureFreeEnvironment) (counter : Fin 64)
    (blocks : List Digest256) (outcome : CandidateOutcome)
    (accepted : environment.decoders.candidate counter blocks =
      some outcome) :
    ∀ count, count < blocks.length →
      environment.decoders.candidate counter (blocks.take count) = none := by
  change decodeCandidateOutcome counter blocks = some outcome at accepted
  intro count strict
  change decodeCandidateOutcome counter (blocks.take count) = none
  exact decodeCandidateOutcome_accepted_is_prefix_minimal
    counter blocks outcome accepted count strict

theorem accepted_future_free_candidate_uses_at_most_eight_blocks
    (environment : FutureFreeEnvironment) (counter : Fin 64)
    (blocks : List Digest256) (outcome : CandidateOutcome)
    (accepted : environment.decoders.candidate counter blocks =
      some outcome) :
    blocks.length ≤ 8 := by
  change decodeCandidateOutcome counter blocks = some outcome at accepted
  have exactBlocks := decodeCandidateOutcome_uses_exact_blocks
    counter blocks outcome accepted
  cases outcome with
  | samplerAbort =>
      change blocks.length = 8 at exactBlocks
      omega
  | schedule schedule =>
      change schedule.blocksUsed = blocks.length at exactBlocks
      rw [← exactBlocks]
      exact schedule.withinSixtyFourDraws

theorem next_q16_counter_some_is_immediate_successor
    (counter next : Fin 64)
    (run : nextQ16Counter? counter = some next) :
    next.val = counter.val + 1 := by
  unfold nextQ16Counter? at run
  split at run
  · exact congrArg Fin.val (Option.some.inj run.symm)
  · simp at run

theorem last_q16_counter_has_no_successor (counter : Fin 64)
    (last : counter.val = 63) :
    nextQ16Counter? counter = none := by
  unfold nextQ16Counter?
  split
  · omega
  · rfl

def decodedScheduleRecord (counter : Fin 64)
    (schedule : QuerySchedule) : DecodedQ16Candidate :=
  { counter := counter, outcome := .schedule schedule }

/-- A certificate for the exact already-discarded part of the q16 scan.  It
begins at counter zero, advances only by `nextQ16Counter?`, and records only
exact decoder results whose K1.2 frontier is noncompact.  Sampler aborts
therefore cannot be silently skipped by this history. -/
inductive Q16PriorNoncompactHistory (environment : FutureFreeEnvironment) :
    Fin 64 → List DecodedQ16Candidate → Prop where
  | start : Q16PriorNoncompactHistory environment 0 []
  | step {counter next : Fin 64}
      {records : List DecodedQ16Candidate} (blocks : List Digest256)
      (schedule : QuerySchedule)
      (prior : Q16PriorNoncompactHistory environment counter records)
      (decoded : environment.decoders.candidate counter blocks =
        some (.schedule schedule))
      (noncompact : 203 < environment.frontierNodes schedule)
      (successor : nextQ16Counter? counter = some next) :
      Q16PriorNoncompactHistory environment next
        (records ++ [decodedScheduleRecord counter schedule])

theorem q16_prior_noncompact_history_length_is_counter
    (environment : FutureFreeEnvironment) (counter : Fin 64)
    (records : List DecodedQ16Candidate)
    (history : Q16PriorNoncompactHistory environment counter records) :
    records.length = counter.val := by
  induction history with
  | start => rfl
  | @step current next records blocks schedule prior decoded noncompact
      successor ih =>
      rw [List.length_append, ih]
      have nextValue := next_q16_counter_some_is_immediate_successor
        current next successor
      simp only [List.length_singleton]
      omega

theorem q16_prior_noncompact_history_contains_only_earlier_noncompact
    (environment : FutureFreeEnvironment) (counter : Fin 64)
    (records : List DecodedQ16Candidate)
    (history : Q16PriorNoncompactHistory environment counter records) :
    ∀ record ∈ records,
      record.counter.val < counter.val ∧
      ∃ schedule,
        record = decodedScheduleRecord record.counter schedule ∧
        203 < environment.frontierNodes schedule := by
  induction history with
  | start => simp
  | @step current next records blocks schedule prior decoded noncompact
      successor ih =>
      intro record member
      have nextValue := next_q16_counter_some_is_immediate_successor
        current next successor
      rw [List.mem_append] at member
      rcases member with earlier | selected
      · have established := ih record earlier
        rcases established with ⟨counterLt, scheduleWitness⟩
        exact ⟨by omega, scheduleWitness⟩
      · have equal : record = decodedScheduleRecord current schedule := by
          simpa using selected
        subst record
        exact ⟨by simp [decodedScheduleRecord, nextValue],
          schedule, rfl, noncompact⟩

theorem compact_candidate_block_forces_selection
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) (schedule : QuerySchedule)
    (decoded : environment.decoders.candidate counter
      (outputs ++ [output]) = some (.schedule schedule))
    (compact : environment.frontierNodes schedule ≤ 203) :
    processFutureFreeCandidateBlock environment snapshot base counter outputs
      remaining output nextCore =
        { snapshot with
          control := .q16Selected base counter schedule remaining
          core := nextCore
          q16Candidates := snapshot.q16Candidates ++
            [decodedScheduleRecord counter schedule] } := by
  simp only [processFutureFreeCandidateBlock, decoded]
  simp only [compact, if_pos, decodedScheduleRecord]

theorem noncompact_candidate_block_forces_protocol_restore
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) (schedule : QuerySchedule)
    (decoded : environment.decoders.candidate counter
      (outputs ++ [output]) = some (.schedule schedule))
    (noncompact : 203 < environment.frontierNodes schedule) :
    processFutureFreeCandidateBlock environment snapshot base counter outputs
      remaining output nextCore =
        { snapshot with
          control := .q16Restore base counter (nextQ16Counter? counter)
            remaining
          core := nextCore
          q16Candidates := snapshot.q16Candidates ++
            [decodedScheduleRecord counter schedule] } := by
  simp only [processFutureFreeCandidateBlock, decoded]
  have notCompact : ¬ environment.frontierNodes schedule ≤ 203 := by
    omega
  simp only [notCompact, if_false, decodedScheduleRecord]

/-- Combining an exact chronological noncompact history with the next compact
decoder result proves that the selected candidate is the first compact one.
This is a deterministic scan invariant; a later run/bisimulation proof must
derive its history from concrete transitions. -/
theorem q16_history_then_compact_block_is_first_selection
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) (schedule : QuerySchedule)
    (history : Q16PriorNoncompactHistory environment counter
      snapshot.q16Candidates)
    (decoded : environment.decoders.candidate counter
      (outputs ++ [output]) = some (.schedule schedule))
    (compact : environment.frontierNodes schedule ≤ 203) :
    let next := processFutureFreeCandidateBlock environment snapshot base
      counter outputs remaining output nextCore
    next.control = .q16Selected base counter schedule remaining ∧
      next.q16Candidates = snapshot.q16Candidates ++
        [decodedScheduleRecord counter schedule] ∧
      (∀ record ∈ snapshot.q16Candidates,
        record.counter.val < counter.val ∧
        ∃ earlier,
          record = decodedScheduleRecord record.counter earlier ∧
          203 < environment.frontierNodes earlier) ∧
      (∀ count, count < (outputs ++ [output]).length →
        environment.decoders.candidate counter
          ((outputs ++ [output]).take count) = none) := by
  have result := compact_candidate_block_forces_selection environment
    snapshot base counter outputs remaining output nextCore schedule decoded
      compact
  have prior := q16_prior_noncompact_history_contains_only_earlier_noncompact
    environment counter snapshot.q16Candidates history
  have minimal := accepted_future_free_candidate_is_prefix_minimal environment
    counter (outputs ++ [output]) (.schedule schedule) decoded
  rw [result]
  exact ⟨rfl, rfl, prior, minimal⟩

theorem candidate_sampler_abort_forces_rejection
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (decoded : environment.decoders.candidate counter
      (outputs ++ [output]) = some .samplerAbort) :
    (processFutureFreeCandidateBlock environment snapshot base counter outputs
      remaining output nextCore).control =
        .q16SamplerReject counter (.q16SamplerAbort counter) := by
  simp only [processFutureFreeCandidateBlock, decoded]

theorem candidate_cap_without_decode_forces_rejection
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (undecoded : environment.decoders.candidate counter
      (outputs ++ [output]) = none)
    (atCap : 8 ≤ (outputs ++ [output]).length) :
    (processFutureFreeCandidateBlock environment snapshot base counter outputs
      remaining output nextCore).control =
        .q16SamplerReject counter (.q16DecoderCap counter) := by
  simp only [processFutureFreeCandidateBlock, undecoded]
  have notBelow : ¬ (outputs ++ [output]).length < 8 := by omega
  simp only [notBelow, if_false]

theorem challenge_cap_without_decode_forces_rejection
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore)
    (undecoded : environment.decoders.qm31Parameter id
      (outputs ++ [output]) = none)
    (atCap : samplerBlockCap (samplerMode id) ≤
      (outputs ++ [output]).length) :
    (processFutureFreeChallengeBlock environment snapshot id outputs remaining
      output nextCore).control = .rejected (.challengeSamplerCap id) := by
  simp only [processFutureFreeChallengeBlock, undecoded]
  have notBelow : ¬ (outputs ++ [output]).length <
      samplerBlockCap (samplerMode id) := by omega
  simp only [notBelow, if_false]

/-! ## Explicit boundary to semantic acceptance

The controller above establishes transcript order and exact byte-level public
coin consumption.  Its checkpoint and terminal actions are deliberately
operational markers: they do not prove the semantic claims, either Merkle
authentication, or the terminal relation.  Those checks are the typed K1.2--
K1.5 acceptance layer, listed here so schedule exhaustion cannot be confused
with acceptance. -/

inductive FutureFreeExternalAcceptanceObligation where
  | semanticAndPointClaims
  | initialC1Authentication
  | foldedC2Authentication
  | exactSelectedFrontier
  | terminalRelation
  deriving DecidableEq, Repr

def futureFreeExternalAcceptanceObligations :
    List FutureFreeExternalAcceptanceObligation :=
  [.semanticAndPointClaims,
   .initialC1Authentication,
   .foldedC2Authentication,
   .exactSelectedFrontier,
   .terminalRelation]

def FutureFreeScheduleExhausted (snapshot : FutureFreeSnapshot) : Prop :=
  snapshot.control = .done

theorem checkpoint_action_is_only_an_operational_marker
    (core : RuntimeCore) (checkpoint : Checkpoint) :
    applyActionWorkErased core (.checkpoint checkpoint) .none = some core := by
  rfl

theorem terminal_action_is_only_an_operational_marker
    (core : RuntimeCore) :
    applyActionWorkErased core .terminal .none = some core := by
  rfl

/-! ## The one saved q16 base is preserved by every branch primitive -/

theorem future_free_q16_absorb_preserves_saved_base
    (core next : RuntimeCore) (base output : Digest256)
    (counter : Fin 64) (saved : core.q16Base = some base)
    (run : applyActionWorkErased core (.absorb (.queryCandidate counter))
      (.single output) = some next) :
    next.q16Base = some base := by
  simp [applyActionWorkErased] at run
  subst next
  simpa [saved] using saved

theorem future_free_q16_squeeze_preserves_saved_base
    (core next : RuntimeCore) (base output advance : Digest256)
    (counter : Fin 64) (block : Nat)
    (saved : core.q16Base = some base)
    (run : applyActionWorkErased core
      (.squeezePair (.queryCandidate counter) block)
      (.squeeze output advance) = some next) :
    next.q16Base = some base := by
  simp [applyActionWorkErased] at run
  subst next
  simpa [saved] using saved

theorem future_free_q16_restore_reinstalls_saved_base
    (core next : RuntimeCore) (base : Digest256) (counter : Fin 64)
    (saved : core.q16Base = some base)
    (run : applyActionWorkErased core (.q16Restore counter) .none =
      some next) :
    next.digest = base ∧ next.q16Base = some base :=
  q16_restore_returns_to_saved_base core next counter base saved run

/-! ## One forced verifier step -/

def rawAfterFutureFreeVerifierReply (environment : FutureFreeEnvironment)
    (snapshot : FutureFreeSnapshot) (reply : VerifierReply)
    (nextCore : RuntimeCore) : Option FutureFreeSnapshot :=
  match snapshot.control, reply with
  | .adaptive control, reply => do
      let nextAdaptive ← control.afterVerifierReply environment.decoders reply
      let decoded :=
        match control, nextAdaptive with
        | .sampleLambda _, .sampleChi lambda _ =>
            snapshot.decodedChallenges ++ [{ id := .lambda, value := lambda }]
        | .sampleChi _ _, .awaitingC2 _ chi =>
            snapshot.decodedChallenges ++ [{ id := .chi, value := chi }]
        | _, _ => snapshot.decodedChallenges
      let nextControl :=
        match nextAdaptive with
        | .afterAdaptiveC2 _ _ => .linear fullFutureFreeSlots
        | _ => .adaptive nextAdaptive
      pure
        { snapshot with
          control := nextControl
          core := nextCore
          decodedChallenges := decoded }
  | .linear (.fixed _ :: remaining), _ =>
      some { snapshot with control := linearOrDone remaining, core := nextCore }
  | .linear (.challenge id :: remaining), .squeeze output _ =>
      some (processFutureFreeChallengeBlock environment snapshot id [] remaining
        output nextCore)
  | .linear (.beginQ16 :: remaining), .none =>
      some
        { snapshot with
          control := .q16Absorb nextCore.digest 0 remaining
          core := nextCore }
  | .absorbPayload _ remaining, .single _ =>
      some { snapshot with control := linearOrDone remaining, core := nextCore }
  | .workCheck stage nonce remaining, .single _ =>
      some
        { snapshot with
          control := .workCheckpoint stage nonce remaining
          core := nextCore
          checkedWorkNonces := snapshot.checkedWorkNonces ++
            [{ stage := stage, nonce := nonce }] }
  | .workCheckpoint stage nonce remaining, .none =>
      some
        { snapshot with
          control := .workAbsorb stage nonce remaining
          core := nextCore }
  | .workAbsorb _ _ remaining, .single _ =>
      some { snapshot with control := linearOrDone remaining, core := nextCore }
  | .sampleChallenge id outputs remaining, .squeeze output _ =>
      some (processFutureFreeChallengeBlock environment snapshot id outputs
        remaining output nextCore)
  | .q16Absorb base counter remaining, .single _ =>
      some
        { snapshot with
          control := .q16Sample base counter [] remaining
          core := nextCore }
  | .q16Sample base counter outputs remaining, .squeeze output _ =>
      some (processFutureFreeCandidateBlock environment snapshot base counter
        outputs remaining output nextCore)
  | .q16Restore base _ nextCounter remaining, .none =>
      let control :=
        match nextCounter with
        | some counter => .q16Absorb base counter remaining
        | none => .q16AllNoncompactReject
      some { snapshot with control := control, core := nextCore }
  | .q16Selected _ _ _ remaining, .none =>
      some { snapshot with control := linearOrDone remaining, core := nextCore }
  | .q16SamplerReject _ reason, .none =>
      some { snapshot with control := .rejected reason, core := nextCore }
  | .q16AllNoncompactReject, .none =>
      some
        { snapshot with
          control := .rejected .q16AllNoncompact
          core := nextCore }
  | _, _ => none

/-- Fixed instance data is copied from the restored snapshot after every
raw control update.  The update cannot install caller-selected bindings. -/
def afterFutureFreeVerifierReply (environment : FutureFreeEnvironment)
    (snapshot : FutureFreeSnapshot) (reply : VerifierReply)
    (nextCore : RuntimeCore) : Option FutureFreeSnapshot :=
  (rawAfterFutureFreeVerifierReply environment snapshot reply nextCore).map
    fun next => { next with bindings := snapshot.bindings }

def advanceFutureFreeVerifier (environment : FutureFreeEnvironment)
    (state : FutureFreeVerifierState) (reply : VerifierReply) :
    Option FutureFreeVerifierState := do
  let action ← state.current.control.nextVerifierAction?
  let nextCore ← applyActionWorkErased state.current.core action reply
  let next ← afterFutureFreeVerifierReply environment state.current reply nextCore
  pure (appendFutureFreeSnapshot state (.verifier action reply) next)

/-- The strict deployed-action variant is used only to prove monotonicity into
the work-erased knowledge ancestor. -/
def advanceFutureFreeVerifierStrict (environment : FutureFreeEnvironment)
    (state : FutureFreeVerifierState) (reply : VerifierReply) :
    Option FutureFreeVerifierState := do
  let action ← state.current.control.nextVerifierAction?
  let nextCore ← applyActionStrict state.current.core action reply
  let next ← afterFutureFreeVerifierReply environment state.current reply nextCore
  pure (appendFutureFreeSnapshot state (.verifier action reply) next)

theorem after_future_free_reply_preserves_bindings
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (run : afterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    next.bindings = snapshot.bindings := by
  unfold afterFutureFreeVerifierReply at run
  cases raw : rawAfterFutureFreeVerifierReply environment snapshot reply
      nextCore with
  | none => simp [raw] at run
  | some candidate =>
      rw [raw] at run
      have equal : { candidate with bindings := snapshot.bindings } = next :=
        Option.some.inj run
      rw [← equal]

theorem successful_future_free_advance_uses_forced_action
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (run : advanceFutureFreeVerifier environment state reply = some next) :
    ∃ action,
      state.current.control.nextVerifierAction? = some action ∧
      applyActionWorkErased state.current.core action reply ≠ none := by
  rw [advanceFutureFreeVerifier] at run
  obtain ⟨action, actionEq, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextCore, coreEq, _⟩ := Option.bind_eq_some_iff.mp run
  exact ⟨action, actionEq, by rw [coreEq]; simp⟩

theorem strict_future_free_advance_survives_work_erasure
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (run : advanceFutureFreeVerifierStrict environment state reply =
      some next) :
    advanceFutureFreeVerifier environment state reply = some next := by
  rw [advanceFutureFreeVerifierStrict] at run
  obtain ⟨action, actionEq, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextCore, strictCore, run⟩ := Option.bind_eq_some_iff.mp run
  have erasedCore := strict_action_success_survives_work_erasure
    state.current.core nextCore action reply strictCore
  rw [advanceFutureFreeVerifier]
  exact Option.bind_eq_some_iff.mpr ⟨action, actionEq,
    Option.bind_eq_some_iff.mpr ⟨nextCore, erasedCore, run⟩⟩

theorem successful_future_free_advance_preserves_bindings
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (run : advanceFutureFreeVerifier environment state reply = some next) :
    next.current.bindings = state.current.bindings := by
  rw [advanceFutureFreeVerifier] at run
  obtain ⟨action, actionEq, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextCore, coreEq, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextSnapshot, snapshotEq, finalEq⟩ :=
    Option.bind_eq_some_iff.mp run
  have preserved := after_future_free_reply_preserves_bindings environment
    state.current nextSnapshot reply nextCore snapshotEq
  have nextEq := Option.some.inj finalEq
  subst next
  exact preserved

#print axioms work_stages_are_exactly_batch_fold_final
#print axioms submitted_c2_is_indexed_by_current_decoded_values
#print axioms accepted_future_free_challenge_is_prefix_minimal
#print axioms accepted_future_free_candidate_is_prefix_minimal
#print axioms accepted_future_free_candidate_uses_at_most_eight_blocks
#print axioms q16_prior_noncompact_history_length_is_counter
#print axioms q16_prior_noncompact_history_contains_only_earlier_noncompact
#print axioms q16_history_then_compact_block_is_first_selection
#print axioms candidate_sampler_abort_forces_rejection
#print axioms candidate_cap_without_decode_forces_rejection
#print axioms checkpoint_action_is_only_an_operational_marker
#print axioms terminal_action_is_only_an_operational_marker
#print axioms future_free_q16_restore_reinstalls_saved_base
#print axioms strict_future_free_advance_survives_work_erasure
#print axioms successful_future_free_advance_preserves_bindings

end

end AspisK1.V7Tag73FutureFreeFullControl
