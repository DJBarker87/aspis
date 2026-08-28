import AspisFormal.K1.V7Tag73SchedulerHistoryQ16Router
import AspisFormal.K1.V7Tag73FutureFreeQ16ExposureMachine

/-!
# Alignment of the future-free q16 control with root-verifier history

The causal router labels fresh scheduler answers by replaying a tiny automaton
over completed `.verifier` query records.  This file relates that automaton to
the literal future-free controller.  The key invariant is intentionally
partial: only a live `q16Sample` control imposes a history phase.  Every other
control is irrelevant to the next q16 output coordinate.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FutureFreeQ16HistoryAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SchedulerHistoryQ16Router
open AspisK1.V7Tag73SharedOracleVerifierRunner

noncomputable section

/-- The completed verifier query history names the exact next q16 block held
by a live incremental candidate sampler. -/
def FutureFreeQ16HistoryAligned
    (state : FutureFreeVerifierState) (history : List QueryRecord) : Prop :=
  match state.current.control with
  | .q16Sample _base counter outputs _remaining =>
      rootQ16HistoryPhase history = .ready counter outputs.length
  | _ => True

/-- Actor-rich scheduler records realize the actor-free query path emitted by
the future-free oracle program. -/
def VerifierRecordsRealizePairs
    (records : List QueryRecord) (pairs : List (ShaInput × ShaOutput)) : Prop :=
  records.map (fun record => (record.input, record.output)) = pairs ∧
    ∀ record ∈ records, record.actor = .verifier

theorem verifier_records_realize_nil_iff
    (records : List QueryRecord) :
    VerifierRecordsRealizePairs records [] ↔ records = [] := by
  constructor
  · intro realized
    simpa [VerifierRecordsRealizePairs] using
      congrArg List.length realized.1
  · rintro rfl
    simp [VerifierRecordsRealizePairs]

theorem verifier_records_realize_singleton
    (records : List QueryRecord) (input : ShaInput) (output : ShaOutput)
    (realized : VerifierRecordsRealizePairs records [(input, output)]) :
    ∃ origin : AnswerOrigin,
      records = [{ input := input
                   output := output
                   actor := .verifier
                   origin := origin }] := by
  cases records with
  | nil => simp [VerifierRecordsRealizePairs] at realized
  | cons record rest =>
      cases rest with
      | nil =>
          rcases record with ⟨recordInput, recordOutput, actor, origin⟩
          simp [VerifierRecordsRealizePairs] at realized
          rcases realized with
            ⟨⟨inputExact, outputExact⟩, actorExact⟩
          subst recordInput
          subst recordOutput
          exact ⟨origin, by simp [actorExact]⟩
      | cons second tail =>
          simp [VerifierRecordsRealizePairs] at realized

theorem verifier_records_realize_pair
    (records : List QueryRecord)
    (firstInput secondInput : ShaInput)
    (firstOutput secondOutput : ShaOutput)
    (realized : VerifierRecordsRealizePairs records
      [(firstInput, firstOutput), (secondInput, secondOutput)]) :
    ∃ firstOrigin secondOrigin : AnswerOrigin,
      records =
        [{ input := firstInput
           output := firstOutput
           actor := .verifier
           origin := firstOrigin },
         { input := secondInput
           output := secondOutput
           actor := .verifier
           origin := secondOrigin }] := by
  cases records with
  | nil => simp [VerifierRecordsRealizePairs] at realized
  | cons first rest =>
      cases rest with
      | nil => simp [VerifierRecordsRealizePairs] at realized
      | cons second tail =>
          cases tail with
          | nil =>
              rcases first with ⟨firstRecordInput, firstRecordOutput,
                firstActor, firstOrigin⟩
              rcases second with ⟨secondRecordInput, secondRecordOutput,
                secondActor, secondOrigin⟩
              simp [VerifierRecordsRealizePairs] at realized
              rcases realized with
                ⟨⟨⟨firstInputExact, firstOutputExact⟩,
                    secondInputExact, secondOutputExact⟩,
                  firstActorExact, secondActorExact⟩
              subst firstRecordInput
              subst firstRecordOutput
              subst secondRecordInput
              subst secondRecordOutput
              exact ⟨firstOrigin, secondOrigin,
                by simp [firstActorExact, secondActorExact]⟩
          | cons third tail =>
              simp [VerifierRecordsRealizePairs] at realized

/-- A chronological verifier-record realization splits at the same boundary
as the actor-free query path. -/
theorem verifier_records_realize_append_split
    (records : List QueryRecord)
    (head tail : List (ShaInput × ShaOutput))
    (realized : VerifierRecordsRealizePairs records (head ++ tail)) :
    ∃ headRecords tailRecords,
      records = headRecords ++ tailRecords ∧
      VerifierRecordsRealizePairs headRecords head ∧
      VerifierRecordsRealizePairs tailRecords tail := by
  induction head generalizing records with
  | nil =>
      exact ⟨[], records, by simp,
        by simp [VerifierRecordsRealizePairs], by simpa using realized⟩
  | cons pair head inductionHypothesis =>
      cases records with
      | nil => simp [VerifierRecordsRealizePairs] at realized
      | cons record records =>
          have mapped := realized.1
          change (record.input, record.output) ::
              records.map (fun entry => (entry.input, entry.output)) =
            pair :: (head ++ tail) at mapped
          have mappedParts := List.cons.inj mapped
          have recordActor : record.actor = .verifier :=
            realized.2 record (by simp)
          have restRealized :
              VerifierRecordsRealizePairs records (head ++ tail) := by
            refine ⟨mappedParts.2, ?_⟩
            intro entry member
            exact realized.2 entry (by simp [member])
          obtain ⟨headRecords, tailRecords, recordsExact,
              headRealized, tailRealized⟩ :=
            inductionHypothesis records restRealized
          refine ⟨record :: headRecords, tailRecords, ?_, ?_, tailRealized⟩
          · simp [recordsExact]
          · constructor
            · simp [mappedParts.1, headRealized.1]
            · intro entry member
              rcases List.mem_cons.mp member with entryExact | member
              · subst entry
                exact recordActor
              · exact headRealized.2 entry member

/-- The q16 absorb oracle program has one literal query and one literal
single-output reply. -/
theorem q16_absorb_reply_path_exact
    (state : FutureFreeVerifierState) (counter : Fin 64)
    (pairs : List (ShaInput × ShaOutput)) (reply : VerifierReply)
    (path : MachineQueryPath
      (futureFreeReplyProgram state (.absorb (.queryCandidate counter)))
      pairs reply) :
    ∃ output,
      pairs = [(bytes state.current.core.digest ++
        [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val], output)] ∧
      reply = .single output := by
  change MachineQueryPath
    (.query (bytes state.current.core.digest ++
      [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]) fun output =>
        .pure (.single output)) pairs reply at path
  cases path with
  | query _input _next output tailPairs result tail =>
      cases tail
      exact ⟨output, rfl, rfl⟩

/-- The q16 sample oracle program has the literal adjacent squeeze and
advance queries and returns their paired reply. -/
theorem q16_sample_reply_path_exact
    (state : FutureFreeVerifierState) (counter : Fin 64) (block : Nat)
    (pairs : List (ShaInput × ShaOutput)) (reply : VerifierReply)
    (path : MachineQueryPath
      (futureFreeReplyProgram state
        (.squeezePair (.queryCandidate counter) block)) pairs reply) :
    ∃ output advance,
      pairs =
        [(bytes state.current.core.digest ++ [domSqueeze], output),
         (bytes state.current.core.digest ++ [domAdvance], advance)] ∧
      reply = .squeeze output advance := by
  change MachineQueryPath
    (.query (bytes state.current.core.digest ++ [domSqueeze]) fun output =>
      .query (bytes state.current.core.digest ++ [domAdvance]) fun advance =>
        .pure (.squeeze output advance)) pairs reply at path
  cases path with
  | query _input _next output tailPairs result tail =>
      cases tail with
      | query _input _next advance tailPairs result tail =>
          cases tail
          exact ⟨output, advance, rfl, rfl⟩

@[simp] theorem initial_future_free_q16_history_aligned
    (bindings : FixedBindings) (history : List QueryRecord) :
    FutureFreeQ16HistoryAligned
      (initialFutureFreeVerifierState bindings) history := by
  simp [FutureFreeQ16HistoryAligned, initialFutureFreeVerifierState,
    initialFutureFreeSnapshot]

/-- Prover-owned zero-query submissions cannot create an incremental q16
sample control. -/
theorem submit_next_raw_message_preserves_q16_history_alignment
    (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState) (history : List QueryRecord)
    (aligned : FutureFreeQ16HistoryAligned state history)
    (submitted : submitNextRawMessage raw state = some next) :
    FutureFreeQ16HistoryAligned next history := by
  unfold submitNextRawMessage at submitted
  split at submitted
  next controlExact =>
    unfold submitFutureFreeC1 at submitted
    split at submitted
    next =>
      have nextExact := Option.some.inj submitted
      rw [← nextExact]
      simp [FutureFreeQ16HistoryAligned, appendFutureFreeSnapshot]
    all_goals simp at submitted
  next lambda chi controlExact =>
    have nextExact := Option.some.inj submitted
    rw [← nextExact]
    simp [submitFutureFreeC2, FutureFreeQ16HistoryAligned,
      appendFutureFreeSnapshot]
  next site remaining controlExact =>
    unfold submitFutureFreePayload at submitted
    split at submitted
    next =>
      split at submitted
      next =>
        have nextExact := Option.some.inj submitted
        rw [← nextExact]
        simp [FutureFreeQ16HistoryAligned, appendFutureFreeSnapshot]
      next => simp at submitted
    all_goals simp at submitted
  next stage remaining controlExact =>
    unfold submitFutureFreeWorkNonce at submitted
    split at submitted
    next =>
      have nextExact := Option.some.inj submitted
      rw [← nextExact]
      simp [FutureFreeQ16HistoryAligned, appendFutureFreeSnapshot]
    all_goals simp at submitted
  all_goals simp at submitted

/-! ## Exact q16 verifier cases -/

/-- Completing the candidate-absorb query starts block zero in both the
controller and the history automaton. -/
theorem q16_absorb_reply_aligns_history
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState)
    (history : List QueryRecord)
    (base output : Digest256) (counter : Fin 64)
    (remaining : List FutureFreeSlot) (origin : AnswerOrigin)
    (controlExact : state.current.control =
      .q16Absorb base counter remaining)
    (advanced : advanceFutureFreeVerifier environment state (.single output) =
      some next) :
    FutureFreeQ16HistoryAligned next
      (history ++ [{ input := bytes state.current.core.digest ++
          [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]
                     output := output
                     actor := .verifier
                     origin := origin }]) := by
  let nextCore : RuntimeCore :=
    { state.current.core with digest := output }
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .q16Sample base counter [] remaining
      core := nextCore }
  have nextExact : next = appendFutureFreeSnapshot state
      (.verifier (.absorb (.queryCandidate counter)) (.single output))
      nextSnapshot := by
    simpa [advanceFutureFreeVerifier, controlExact, applyActionWorkErased,
      afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      FutureFreeControl.nextVerifierAction?, nextCore, nextSnapshot] using
        advanced.symm
  rw [nextExact]
  simp [FutureFreeQ16HistoryAligned, appendFutureFreeSnapshot,
    nextSnapshot, RootQ16HistoryPhase.afterVerifierInput]

/-- A completed q16 squeeze/advance pair increments the history block exactly
when the literal bounded decoder asks the controller for another block.  If
the decoder returns or reaches its cap, the next control is not `q16Sample`
and the alignment obligation is vacuous. -/
theorem q16_sample_reply_preserves_history_alignment
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState)
    (history : List QueryRecord)
    (base output advance : Digest256) (counter : Fin 64)
    (outputs : List Digest256) (remaining : List FutureFreeSlot)
    (outputOrigin advanceOrigin : AnswerOrigin)
    (controlExact : state.current.control =
      .q16Sample base counter outputs remaining)
    (aligned : FutureFreeQ16HistoryAligned state history)
    (advanced : advanceFutureFreeVerifier environment state
      (.squeeze output advance) = some next) :
    FutureFreeQ16HistoryAligned next
      (history ++
        [{ input := bytes state.current.core.digest ++ [domSqueeze]
           output := output
           actor := .verifier
           origin := outputOrigin },
         { input := bytes state.current.core.digest ++ [domAdvance]
           output := advance
           actor := .verifier
           origin := advanceOrigin }]) := by
  let nextCore : RuntimeCore :=
    { state.current.core with digest := advance }
  let processed : FutureFreeSnapshot :=
    processFutureFreeCandidateBlock environment state.current base counter
      outputs remaining output nextCore
  let nextSnapshot : FutureFreeSnapshot :=
    { processed with bindings := state.current.bindings }
  have nextExact : next = appendFutureFreeSnapshot state
      (.verifier (.squeezePair (.queryCandidate counter) outputs.length)
        (.squeeze output advance)) nextSnapshot := by
    simpa [advanceFutureFreeVerifier, controlExact, applyActionWorkErased,
      afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      FutureFreeControl.nextVerifierAction?, nextCore, processed,
      nextSnapshot] using advanced.symm
  rw [nextExact]
  have phaseExact : rootQ16HistoryPhase history =
      .ready counter outputs.length := by
    simpa [FutureFreeQ16HistoryAligned, controlExact] using aligned
  have phaseAfterPair :
      rootQ16HistoryPhase
          (history ++
            [{ input := bytes state.current.core.digest ++ [domSqueeze]
               output := output
               actor := .verifier
               origin := outputOrigin },
             { input := bytes state.current.core.digest ++ [domAdvance]
               output := advance
               actor := .verifier
               origin := advanceOrigin }]) =
        .ready counter (outputs.length + 1) := by
    rw [show history ++
        [{ input := bytes state.current.core.digest ++ [domSqueeze]
           output := output
           actor := .verifier
           origin := outputOrigin },
         { input := bytes state.current.core.digest ++ [domAdvance]
           output := advance
           actor := .verifier
           origin := advanceOrigin }] =
        (history ++
          [{ input := bytes state.current.core.digest ++ [domSqueeze]
             output := output
             actor := .verifier
             origin := outputOrigin }]) ++
          [{ input := bytes state.current.core.digest ++ [domAdvance]
             output := advance
             actor := .verifier
             origin := advanceOrigin }] by simp]
    rw [root_q16_history_phase_append_verifier,
      root_q16_history_phase_append_verifier, phaseExact]
    simp [RootQ16HistoryPhase.afterVerifierInput,
      q16CandidateCounterOfInput?, isTag73SqueezeInput,
      isTag73AdvanceInput]
  cases decoded : environment.decoders.candidate counter
      (outputs ++ [output]) with
  | some outcome =>
      cases outcome with
      | samplerAbort =>
          simp [FutureFreeQ16HistoryAligned, appendFutureFreeSnapshot,
            nextSnapshot, processed, processFutureFreeCandidateBlock,
            decoded]
      | schedule schedule =>
          by_cases compact : environment.frontierNodes schedule ≤ 203
          · simp [FutureFreeQ16HistoryAligned, appendFutureFreeSnapshot,
              nextSnapshot, processed, processFutureFreeCandidateBlock,
              decoded, compact]
          · simp [FutureFreeQ16HistoryAligned, appendFutureFreeSnapshot,
              nextSnapshot, processed, processFutureFreeCandidateBlock,
              decoded, compact]
  | none =>
      by_cases belowCap : (outputs ++ [output]).length < 8
      · have belowCap' : outputs.length + 1 < 8 := by simpa using belowCap
        simp [FutureFreeQ16HistoryAligned, appendFutureFreeSnapshot,
          nextSnapshot, processed, processFutureFreeCandidateBlock, decoded,
          belowCap', phaseAfterPair]
      · have belowCap' : ¬ outputs.length + 1 < 8 := by
          simpa using belowCap
        simp [FutureFreeQ16HistoryAligned, appendFutureFreeSnapshot,
          nextSnapshot, processed, processFutureFreeCandidateBlock, decoded,
          belowCap']

/-- A live bounded q16 sampler state and its proved chronological history
alignment determine the exact pre-answer slot used by the deployed history
router.  The fresh output is not an argument: only the completed history and
the literal squeeze input select `(counter, outputs.length)`. -/
theorem history_aligned_q16_sample_has_exact_preferred_slot
    (state : FutureFreeVerifierState)
    (history : List QueryRecord)
    (base digest : Digest256) (counter : Fin 64)
    (outputs : List Digest256) (remaining : List FutureFreeSlot)
    (controlExact : state.current.control =
      .q16Sample base counter outputs remaining)
    (aligned : FutureFreeQ16HistoryAligned state history)
    (bounded : outputs.length < 8) :
    rootQ16PreferredSlotFromHistory history
        (bytes digest ++ [domSqueeze]) =
      some (counter, ⟨outputs.length, bounded⟩) := by
  have phaseExact : rootQ16HistoryPhase history =
      .ready counter outputs.length := by
    simpa [FutureFreeQ16HistoryAligned, controlExact] using aligned
  exact root_q16_preferred_slot_of_ready_phase history counter outputs.length
    digest phaseExact bounded

/-! ## One complete operational microstep -/

/-- Controls other than `q16Sample` impose no history-alignment obligation. -/
def Q16SampleFree : FutureFreeControl → Prop
  | .q16Sample _ _ _ _ => False
  | _ => True

theorem q16_sample_free_implies_history_alignment
    (state : FutureFreeVerifierState) (history : List QueryRecord)
    (free : Q16SampleFree state.current.control) :
    FutureFreeQ16HistoryAligned state history := by
  cases controlExact : state.current.control <;>
    simp [Q16SampleFree, FutureFreeQ16HistoryAligned, controlExact] at free ⊢

theorem linear_or_done_is_q16_sample_free (remaining : List FutureFreeSlot) :
    Q16SampleFree (linearOrDone remaining) := by
  cases remaining <;> simp [Q16SampleFree, linearOrDone]

/-- Ordinary challenge decoding cannot enter the q16 sampling loop. -/
theorem process_future_free_challenge_block_is_q16_sample_free
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) :
    Q16SampleFree
      (processFutureFreeChallengeBlock environment snapshot id outputs
        remaining output nextCore).control := by
  simp only [processFutureFreeChallengeBlock]
  split
  · unfold completeFutureFreeChallenge
    split <;> (try split) <;> cases remaining <;>
      simp [Q16SampleFree, linearOrDone]
  · split <;> simp [Q16SampleFree]

/-- The adaptive prefix can only remain adaptive or enter the fixed linear
schedule; it cannot jump into q16 sampling. -/
theorem adaptive_reply_is_q16_sample_free
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (control : V7Tag73ResumeDerivedReplayNode.OpenAdaptiveControl)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (controlExact : snapshot.control = .adaptive control)
    (run : afterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    Q16SampleFree next.control := by
  cases nextAdaptiveExact : control.afterVerifierReply environment.decoders reply
  · simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      controlExact, nextAdaptiveExact] at run
  · rename_i nextAdaptive
    simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
      controlExact, nextAdaptiveExact] at run
    subst next
    cases nextAdaptive <;> simp [Q16SampleFree]

/-- A fixed linear verifier slot can enter `q16Absorb`, but never skips the
candidate absorb and enters `q16Sample` directly. -/
theorem linear_reply_is_q16_sample_free
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (remaining : List FutureFreeSlot) (reply : VerifierReply)
    (nextCore : RuntimeCore)
    (controlExact : snapshot.control = .linear remaining)
    (run : afterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    Q16SampleFree next.control := by
  cases remaining with
  | nil =>
      cases reply <;>
        simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
          controlExact] at run
  | cons slot remaining =>
      cases slot <;> cases reply <;>
        simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
          controlExact, Q16SampleFree, linearOrDone] at run ⊢
      case challenge.squeeze id output advance =>
        subst next
        exact process_future_free_challenge_block_is_q16_sample_free
          environment snapshot id [] remaining output nextCore
      all_goals
        subst next
        cases remaining <;> simp

/-- Every literal future-free operational step preserves the history/control
alignment when its actor-rich records are the records of the actor-free query
path. -/
theorem future_free_operational_step_preserves_q16_history_alignment
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (records history : List QueryRecord)
    (step : FutureFreeOperationalStep environment raw state pairs next)
    (realized : VerifierRecordsRealizePairs records pairs)
    (aligned : FutureFreeQ16HistoryAligned state history) :
    FutureFreeQ16HistoryAligned next (history ++ records) := by
  cases step with
  | prover submitted event snapshot appendExact =>
      have recordsExact : records = [] :=
        (verifier_records_realize_nil_iff records).mp realized
      subst records
      simpa using
        submit_next_raw_message_preserves_q16_history_alignment raw state next
          history aligned submitted
  | stutter noSubmission noAction =>
      have recordsExact : records = [] :=
        (verifier_records_realize_nil_iff records).mp realized
      subst records
      simpa using aligned
  | @verifier _ action reply _ forced replyPath advanced =>
      cases controlExact : state.current.control
      case adaptive control =>
          rw [advanceFutureFreeVerifier, forced] at advanced
          obtain ⟨stepAction, _actionExact, advanced⟩ :=
            Option.bind_eq_some_iff.mp advanced
          obtain ⟨nextCore, _coreExact, advanced⟩ :=
            Option.bind_eq_some_iff.mp advanced
          obtain ⟨nextSnapshot, snapshotExact, stateExact⟩ :=
            Option.bind_eq_some_iff.mp advanced
          have stateExact' := Option.some.inj stateExact
          subst next
          apply q16_sample_free_implies_history_alignment
          simpa [appendFutureFreeSnapshot] using
            adaptive_reply_is_q16_sample_free environment state.current
              nextSnapshot control reply nextCore controlExact snapshotExact
      case linear remaining =>
          rw [advanceFutureFreeVerifier, forced] at advanced
          obtain ⟨stepAction, _actionExact, advanced⟩ :=
            Option.bind_eq_some_iff.mp advanced
          obtain ⟨nextCore, _coreExact, advanced⟩ :=
            Option.bind_eq_some_iff.mp advanced
          obtain ⟨nextSnapshot, snapshotExact, stateExact⟩ :=
            Option.bind_eq_some_iff.mp advanced
          have stateExact' := Option.some.inj stateExact
          subst next
          apply q16_sample_free_implies_history_alignment
          simpa [appendFutureFreeSnapshot] using
            linear_reply_is_q16_sample_free environment state.current
              nextSnapshot remaining reply nextCore controlExact snapshotExact
      case q16Absorb base counter remaining =>
          have actionExact : action = .absorb (.queryCandidate counter) := by
            rw [controlExact] at forced
            simpa [FutureFreeControl.nextVerifierAction?] using
              Option.some.inj forced.symm
          subst action
          obtain ⟨output, pairsExact, replyExact⟩ :=
            q16_absorb_reply_path_exact state counter pairs reply replyPath
          subst reply
          subst pairs
          obtain ⟨origin, recordsExact⟩ :=
            verifier_records_realize_singleton records
              (bytes state.current.core.digest ++
                [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val])
              output realized
          subst records
          exact q16_absorb_reply_aligns_history environment state next history
            base output counter remaining origin controlExact advanced
      case q16Sample base counter outputs remaining =>
          have actionExact : action =
              .squeezePair (.queryCandidate counter) outputs.length := by
            rw [controlExact] at forced
            simpa [FutureFreeControl.nextVerifierAction?] using
              Option.some.inj forced.symm
          subst action
          obtain ⟨output, advance, pairsExact, replyExact⟩ :=
            q16_sample_reply_path_exact state counter outputs.length pairs
              reply replyPath
          subst reply
          subst pairs
          obtain ⟨outputOrigin, advanceOrigin, recordsExact⟩ :=
            verifier_records_realize_pair records
              (bytes state.current.core.digest ++ [domSqueeze])
              (bytes state.current.core.digest ++ [domAdvance]) output advance
              realized
          subst records
          exact q16_sample_reply_preserves_history_alignment environment state
            next history base output advance counter outputs remaining
            outputOrigin advanceOrigin controlExact aligned advanced
      all_goals
        rw [advanceFutureFreeVerifier, forced] at advanced
        obtain ⟨stepAction, _actionExact, advanced⟩ :=
          Option.bind_eq_some_iff.mp advanced
        obtain ⟨nextCore, _coreExact, advanced⟩ :=
          Option.bind_eq_some_iff.mp advanced
        obtain ⟨nextSnapshot, snapshotExact, stateExact⟩ :=
          Option.bind_eq_some_iff.mp advanced
        have stateExact' := Option.some.inj stateExact
        subst next
        cases reply <;>
          simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
          controlExact] at snapshotExact
        all_goals
          subst nextSnapshot
          apply q16_sample_free_implies_history_alignment
          simp only [appendFutureFreeSnapshot]
          first
          | exact process_future_free_challenge_block_is_q16_sample_free
              environment state.current _ _ _ _ nextCore
          | exact linear_or_done_is_q16_sample_free _
          | split <;> simp [Q16SampleFree]
          | simp [Q16SampleFree]

/-- The concrete history alignment is invariant across an entire literal
future-free execution, not merely the two q16 actions in isolation. -/
theorem future_free_operational_trace_preserves_q16_history_alignment
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state final : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (records history : List QueryRecord)
    (trace : FutureFreeOperationalTrace environment raw state pairs final)
    (realized : VerifierRecordsRealizePairs records pairs)
    (aligned : FutureFreeQ16HistoryAligned state history) :
    FutureFreeQ16HistoryAligned final (history ++ records) := by
  induction trace generalizing records history with
  | stop current =>
      have recordsExact : records = [] :=
        (verifier_records_realize_nil_iff records).mp realized
      subst records
      simpa using aligned
  | @next state middle final head tail step rest inductionHypothesis =>
      obtain ⟨headRecords, tailRecords, recordsExact,
          headRealized, tailRealized⟩ :=
        verifier_records_realize_append_split records head tail realized
      subst records
      have middleAligned :=
        future_free_operational_step_preserves_q16_history_alignment
          environment raw state middle head headRecords history step
          headRealized aligned
      have finalAligned := inductionHypothesis tailRecords
        (history ++ headRecords) tailRealized middleAligned
      simpa [List.append_assoc] using finalAligned

#print axioms submit_next_raw_message_preserves_q16_history_alignment
#print axioms q16_absorb_reply_aligns_history
#print axioms q16_sample_reply_preserves_history_alignment
#print axioms history_aligned_q16_sample_has_exact_preferred_slot
#print axioms future_free_operational_step_preserves_q16_history_alignment
#print axioms future_free_operational_trace_preserves_q16_history_alignment

end

end AspisK1.V7Tag73FutureFreeQ16HistoryAlignment
