import AspisFormal.K1.V7Tag73RawFutureFreeDriver

/-!
# Query-path provenance of future-free Tag-73 runtime digests

This leaf proves the protocol-local operational half of recursive digest
provenance.  Starting from an arbitrary predicate on the restored entry
core, every current digest, saved q16 base, and transition-before core in a
future-free driver trace is either covered by that entry predicate or is an
answer of an actual oracle query in the literal `MachineQueryPath`.

The result deliberately says `MachineQueryAnswer`, not "fresh answer".  A
separate scheduler/table-history theorem classifies cached answers against an
earlier active coordinate.  Keeping these layers separate avoids smuggling
lookup freshness into the verifier semantics.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FutureFreeGlobalDigestProvenance

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SharedOracleVerifierRunner

noncomputable section

/-! ## Origin predicates -/

def MachineQueryAnswer
    (answer : Digest256) (pairs : List (ShaInput × ShaOutput)) : Prop :=
  ∃ input, (input, answer) ∈ pairs

def DigestHasPathOrigin
    (entryOrigin : Digest256 → Prop)
    (pairs : List (ShaInput × ShaOutput)) (digest : Digest256) : Prop :=
  entryOrigin digest ∨ MachineQueryAnswer digest pairs

def RuntimeCoreHasPathOrigins
    (entryOrigin : Digest256 → Prop)
    (pairs : List (ShaInput × ShaOutput)) (core : RuntimeCore) : Prop :=
  DigestHasPathOrigin entryOrigin pairs core.digest ∧
    ∀ base, core.q16Base = some base →
      DigestHasPathOrigin entryOrigin pairs base

def FutureFreeStateHasPathOrigins
    (entryOrigin : Digest256 → Prop)
    (pairs : List (ShaInput × ShaOutput))
    (state : FutureFreeVerifierState) : Prop :=
  RuntimeCoreHasPathOrigins entryOrigin pairs state.current.core ∧
    ∀ transition ∈ state.transitions,
      RuntimeCoreHasPathOrigins entryOrigin pairs transition.before.core

def ReplyContainsAnswer (answer : Digest256) : VerifierReply → Prop
  | .none => False
  | .single output => answer = output
  | .squeeze output advance => answer = output ∨ answer = advance

theorem machine_query_answer_append_left
    (answer : Digest256) (first second : List (ShaInput × ShaOutput))
    (origin : MachineQueryAnswer answer first) :
    MachineQueryAnswer answer (first ++ second) := by
  rcases origin with ⟨input, member⟩
  exact ⟨input, List.mem_append_left second member⟩

theorem machine_query_answer_append_right
    (answer : Digest256) (first second : List (ShaInput × ShaOutput))
    (origin : MachineQueryAnswer answer second) :
    MachineQueryAnswer answer (first ++ second) := by
  rcases origin with ⟨input, member⟩
  exact ⟨input, List.mem_append_right first member⟩

theorem digest_has_path_origin_append
    (entryOrigin : Digest256 → Prop)
    (first second : List (ShaInput × ShaOutput)) (digest : Digest256)
    (origin : DigestHasPathOrigin entryOrigin first digest) :
    DigestHasPathOrigin entryOrigin (first ++ second) digest := by
  rcases origin with entry | query
  · exact Or.inl entry
  · exact Or.inr (machine_query_answer_append_left digest first second query)

theorem runtime_core_has_path_origins_append
    (entryOrigin : Digest256 → Prop)
    (first second : List (ShaInput × ShaOutput)) (core : RuntimeCore)
    (origins : RuntimeCoreHasPathOrigins entryOrigin first core) :
    RuntimeCoreHasPathOrigins entryOrigin (first ++ second) core := by
  refine ⟨digest_has_path_origin_append entryOrigin first second core.digest
    origins.1, ?_⟩
  intro base saved
  exact digest_has_path_origin_append entryOrigin first second base
    (origins.2 base saved)

/-! ## Replies expose literal path answers -/

private theorem single_query_path_contains_reply
    (input : ShaInput) (pairs : List (ShaInput × ShaOutput))
    (reply : VerifierReply)
    (path : MachineQueryPath
      (.query input fun output => .pure (.single output)) pairs reply) :
    ∀ answer, ReplyContainsAnswer answer reply →
      MachineQueryAnswer answer pairs := by
  cases path with
  | query _ _ output tailPairs result tail =>
      cases tail
      intro answer contained
      exact ⟨input, by simpa [ReplyContainsAnswer] using contained⟩

private theorem single_input_or_abort_path_contains_reply
    (inputs : List ShaInput) (pairs : List (ShaInput × ShaOutput))
    (reply : VerifierReply)
    (path : MachineQueryPath
      (match inputs with
      | [input] => .query input fun output => .pure (.single output)
      | _ => .abort .controllerRefused) pairs reply) :
    ∀ answer, ReplyContainsAnswer answer reply →
      MachineQueryAnswer answer pairs := by
  cases inputs with
  | nil => cases path
  | cons input rest =>
      cases rest with
      | nil => exact single_query_path_contains_reply input pairs reply path
      | cons second more => cases path

/-- Every value carried by a successful verifier reply is literally present
in the exact query path of that forced action.  Structural replies carry no
value, and a squeeze contributes both adjacent query answers. -/
theorem future_free_reply_path_contains_every_reply_answer
    (state : FutureFreeVerifierState) (action : VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (reply : VerifierReply)
    (path : MachineQueryPath (futureFreeReplyProgram state action)
      pairs reply) :
    ∀ answer, ReplyContainsAnswer answer reply →
      MachineQueryAnswer answer pairs := by
  unfold futureFreeReplyProgram at path
  cases structural : structuralFutureFreeReply action with
  | some structuralReply =>
      rw [structural] at path
      cases path
      intro answer contained
      cases action <;> simp [structuralFutureFreeReply] at structural
      all_goals cases structural
      all_goals simp [ReplyContainsAnswer] at contained
  | none =>
      rw [structural] at path
      cases action with
      | squeezePair owner block =>
          cases path with
          | query outputInput _ output tailPairs _ tail =>
              cases tail with
              | query advanceInput _ advance rest _ finish =>
                  cases finish
                  intro answer contained
                  rcases contained with rfl | rfl
                  · exact ⟨bytes state.current.core.digest ++ [domSqueeze],
                      by simp⟩
                  · exact ⟨bytes state.current.core.digest ++ [domAdvance],
                      by simp⟩
      | absorb payload =>
          exact single_input_or_abort_path_contains_reply
            (actionInputs state.current.bindings state.current.core
              (.absorb payload)) pairs reply path
      | requestRootSalt tree =>
          exact single_input_or_abort_path_contains_reply
            (actionInputs state.current.bindings state.current.core
              (.requestRootSalt tree)) pairs reply path
      | absorbC1 root =>
          exact single_input_or_abort_path_contains_reply
            (actionInputs state.current.bindings state.current.core
              (.absorbC1 root)) pairs reply path
      | absorbC2 lambda chi commitment =>
          exact single_input_or_abort_path_contains_reply
            (actionInputs state.current.bindings state.current.core
              (.absorbC2 lambda chi commitment)) pairs reply path
      | workProbe stage nonce kind =>
          exact single_input_or_abort_path_contains_reply
            (actionInputs state.current.bindings state.current.core
              (.workProbe stage nonce kind)) pairs reply path
      | q16CandidateAbsorb counter outcome selected =>
          exact single_input_or_abort_path_contains_reply
            (actionInputs state.current.bindings state.current.core
              (.q16CandidateAbsorb counter outcome selected)) pairs reply path
      | checkpoint checkpoint =>
          simp [structuralFutureFreeReply] at structural
      | markQ16Base => simp [structuralFutureFreeReply] at structural
      | q16Restore counter => simp [structuralFutureFreeReply] at structural
      | q16Selected counter => simp [structuralFutureFreeReply] at structural
      | q16SamplerAbortReject counter =>
          simp [structuralFutureFreeReply] at structural
      | q16AllNoncompactReject =>
          simp [structuralFutureFreeReply] at structural
      | terminal => simp [structuralFutureFreeReply] at structural

/-! ## Runtime-core source classification -/

/-- Work-erased action execution changes the live digest only to a reply
answer or to the previously saved q16 base.  The saved base is either retained
or set to the immediately preceding digest. -/
theorem apply_action_work_erased_core_sources
    (core next : RuntimeCore) (action : VerifierAction)
    (reply : VerifierReply)
    (run : applyActionWorkErased core action reply = some next) :
    (next.digest = core.digest ∨
      ReplyContainsAnswer next.digest reply ∨
      ∃ base, core.q16Base = some base ∧ next.digest = base) ∧
    (∀ base, next.q16Base = some base →
      core.q16Base = some base ∨ base = core.digest) := by
  cases action with
  | absorb payload =>
      cases reply <;> simp [applyActionWorkErased] at run
      rename_i output
      subst next
      exact ⟨Or.inr (Or.inl rfl), fun base saved => Or.inl saved⟩
  | requestRootSalt tree =>
      cases tree <;> cases reply <;>
        simp [applyActionWorkErased] at run
      all_goals rename_i output
      all_goals subst next
      all_goals exact ⟨Or.inl rfl, fun base saved => Or.inl saved⟩
  | absorbC1 root =>
      cases reply <;> simp [applyActionWorkErased] at run
      rename_i output
      cases salt : core.c1Salt <;> simp [salt] at run
      subst next
      exact ⟨Or.inr (Or.inl rfl), fun base saved => Or.inl saved⟩
  | absorbC2 lambda chi commitment =>
      cases reply <;> simp [applyActionWorkErased] at run
      rename_i output
      cases salt : core.c2Salt <;> simp [salt] at run
      subst next
      exact ⟨Or.inr (Or.inl rfl), fun base saved => Or.inl saved⟩
  | squeezePair owner block =>
      cases reply <;> simp [applyActionWorkErased] at run
      rename_i output advance
      subst next
      exact ⟨Or.inr (Or.inl (Or.inr rfl)),
        fun base saved => Or.inl saved⟩
  | workProbe stage nonce kind =>
      cases reply <;> simp [applyActionWorkErased] at run
      rename_i output
      subst next
      exact ⟨Or.inl rfl, fun base saved => Or.inl saved⟩
  | checkpoint checkpoint =>
      cases reply <;> simp [applyActionWorkErased] at run
      subst next
      exact ⟨Or.inl rfl, fun base saved => Or.inl saved⟩
  | markQ16Base =>
      cases reply <;> simp [applyActionWorkErased] at run
      subst next
      refine ⟨Or.inl rfl, ?_⟩
      intro base saved
      simp at saved
      subst base
      exact Or.inr rfl
  | q16CandidateAbsorb counter outcome selected =>
      cases reply <;> simp [applyActionWorkErased] at run
      rename_i output
      cases savedBase : core.q16Base <;> simp [savedBase] at run
      rename_i savedValue
      subst next
      refine ⟨Or.inr (Or.inl rfl), ?_⟩
      intro base saved
      simp at saved
      subst base
      exact Or.inl rfl
  | q16Restore counter =>
      cases reply <;> simp [applyActionWorkErased] at run
      cases savedBase : core.q16Base <;> simp [savedBase] at run
      rename_i savedValue
      subst next
      refine ⟨Or.inr (Or.inr ⟨savedValue, rfl, rfl⟩), ?_⟩
      intro base saved
      simp at saved
      subst base
      exact Or.inl rfl
  | q16Selected counter =>
      cases reply <;> simp [applyActionWorkErased] at run
      subst next
      exact ⟨Or.inl rfl, fun base saved => Or.inl saved⟩
  | q16SamplerAbortReject counter =>
      cases reply <;> simp [applyActionWorkErased] at run
      subst next
      exact ⟨Or.inl rfl, fun base saved => Or.inl saved⟩
  | q16AllNoncompactReject =>
      cases reply <;> simp [applyActionWorkErased] at run
      subst next
      exact ⟨Or.inl rfl, fun base saved => Or.inl saved⟩
  | terminal =>
      cases reply <;> simp [applyActionWorkErased] at run
      subst next
      exact ⟨Or.inl rfl, fun base saved => Or.inl saved⟩

/-- One successful action preserves both current-digest and saved-q16-base
origins, extending the chronological query list by precisely the action path. -/
theorem apply_action_work_erased_preserves_path_origins
    (entryOrigin : Digest256 → Prop)
    (prior actionPairs : List (ShaInput × ShaOutput))
    (state : FutureFreeVerifierState) (next : RuntimeCore)
    (action : VerifierAction)
    (reply : VerifierReply)
    (priorOrigins : RuntimeCoreHasPathOrigins entryOrigin prior
      state.current.core)
    (path : MachineQueryPath (futureFreeReplyProgram state action)
      actionPairs reply)
    (run : applyActionWorkErased state.current.core action reply = some next) :
    RuntimeCoreHasPathOrigins entryOrigin (prior ++ actionPairs) next := by
  have sources := apply_action_work_erased_core_sources state.current.core next
    action reply run
  have replyAnswers := future_free_reply_path_contains_every_reply_answer
    state action actionPairs reply path
  constructor
  · rcases sources.1 with unchanged | fromReply | restored
    · rw [unchanged]
      exact digest_has_path_origin_append entryOrigin prior actionPairs
        state.current.core.digest priorOrigins.1
    · exact Or.inr (machine_query_answer_append_right next.digest prior
        actionPairs (replyAnswers next.digest fromReply))
    · rcases restored with ⟨restoredBase, saved, digestExact⟩
      rw [digestExact]
      exact digest_has_path_origin_append entryOrigin prior actionPairs
        restoredBase (priorOrigins.2 restoredBase saved)
  · intro base saved
    rcases sources.2 base saved with retained | installed
    · exact digest_has_path_origin_append entryOrigin prior actionPairs base
        (priorOrigins.2 base retained)
    · rw [installed]
      exact digest_has_path_origin_append entryOrigin prior actionPairs
        state.current.core.digest priorOrigins.1

/-! ## Complete-state core projection -/

@[simp] theorem complete_future_free_challenge_core
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (value : Qm31Bytes)
    (remaining : List FutureFreeSlot) (nextCore : RuntimeCore) :
    (completeFutureFreeChallenge environment snapshot id value remaining
      nextCore).core = nextCore := by
  cases id <;> simp [completeFutureFreeChallenge]
  split <;> rfl

@[simp] theorem process_future_free_challenge_block_core
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (id : ChallengeId) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) :
    (processFutureFreeChallengeBlock environment snapshot id outputs remaining
      output nextCore).core = nextCore := by
  simp only [processFutureFreeChallengeBlock]
  split
  · simp
  · split <;> rfl

@[simp] theorem process_future_free_candidate_block_core
    (environment : FutureFreeEnvironment) (snapshot : FutureFreeSnapshot)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (output : Digest256)
    (nextCore : RuntimeCore) :
    (processFutureFreeCandidateBlock environment snapshot base counter outputs
      remaining output nextCore).core = nextCore := by
  simp only [processFutureFreeCandidateBlock]
  split
  · rfl
  · split <;> rfl
  · split <;> rfl

theorem raw_after_future_free_reply_has_exact_core
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (run : rawAfterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    next.core = nextCore := by
  unfold rawAfterFutureFreeVerifierReply at run
  split at run
  next control reply =>
    obtain ⟨nextAdaptive, _advanced, final⟩ := Option.bind_eq_some_iff.mp run
    have nextExact := Option.some.inj final
    rw [← nextExact]
  all_goals
    try {
      have nextExact := Option.some.inj run
      subst next <;> simp }
  all_goals
    try { simp_all }

theorem after_future_free_reply_has_exact_core
    (environment : FutureFreeEnvironment) (snapshot next : FutureFreeSnapshot)
    (reply : VerifierReply) (nextCore : RuntimeCore)
    (run : afterFutureFreeVerifierReply environment snapshot reply nextCore =
      some next) :
    next.core = nextCore := by
  unfold afterFutureFreeVerifierReply at run
  cases raw : rawAfterFutureFreeVerifierReply environment snapshot reply
      nextCore with
  | none => simp [raw] at run
  | some candidate =>
      rw [raw] at run
      have nextExact : { candidate with bindings := snapshot.bindings } = next :=
        Option.some.inj run
      rw [← nextExact]
      exact raw_after_future_free_reply_has_exact_core environment snapshot
        candidate reply nextCore raw

/-- Invert one successful complete verifier advance to the exact core update
used by its appended snapshot. -/
theorem successful_future_free_advance_has_exact_core_run
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (advanced : advanceFutureFreeVerifier environment state reply = some next) :
    ∃ action nextCore,
      state.current.control.nextVerifierAction? = some action ∧
      applyActionWorkErased state.current.core action reply = some nextCore ∧
      next.current.core = nextCore := by
  rw [advanceFutureFreeVerifier] at advanced
  obtain ⟨action, forced, advanced⟩ := Option.bind_eq_some_iff.mp advanced
  obtain ⟨nextCore, coreRun, advanced⟩ := Option.bind_eq_some_iff.mp advanced
  obtain ⟨snapshot, snapshotRun, final⟩ := Option.bind_eq_some_iff.mp advanced
  have finalExact := Option.some.inj final
  subst next
  refine ⟨action, nextCore, forced, coreRun, ?_⟩
  simpa [appendFutureFreeSnapshot] using
    after_future_free_reply_has_exact_core environment state.current snapshot
      reply nextCore snapshotRun

theorem successful_future_free_advance_has_exact_components
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (advanced : advanceFutureFreeVerifier environment state reply = some next) :
    ∃ action nextCore snapshot,
      state.current.control.nextVerifierAction? = some action ∧
      applyActionWorkErased state.current.core action reply = some nextCore ∧
      afterFutureFreeVerifierReply environment state.current reply nextCore =
        some snapshot ∧
      next = appendFutureFreeSnapshot state (.verifier action reply) snapshot := by
  rw [advanceFutureFreeVerifier] at advanced
  obtain ⟨action, forced, advanced⟩ := Option.bind_eq_some_iff.mp advanced
  obtain ⟨nextCore, coreRun, advanced⟩ := Option.bind_eq_some_iff.mp advanced
  obtain ⟨snapshot, snapshotRun, final⟩ := Option.bind_eq_some_iff.mp advanced
  exact ⟨action, nextCore, snapshot, forced, coreRun, snapshotRun,
    (Option.some.inj final).symm⟩

/-- Raw prover submissions change only control/message accumulators; they do
not change the transcript runtime core. -/
theorem successful_raw_submission_preserves_runtime_core
    (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (submitted : submitNextRawMessage raw state = some next) :
    next.current.core = state.current.core := by
  unfold submitNextRawMessage at submitted
  split at submitted <;>
    simp_all [submitFutureFreeC1, submitFutureFreeC2,
      submitFutureFreePayload, submitFutureFreeWorkNonce,
      appendFutureFreeSnapshot]
  all_goals subst next <;> rfl

/-! ## Operational steps and traces -/

theorem append_future_free_snapshot_preserves_path_origins
    (entryOrigin : Digest256 → Prop)
    (prior suffix : List (ShaInput × ShaOutput))
    (state : FutureFreeVerifierState) (event : FutureFreeEvent)
    (snapshot : FutureFreeSnapshot)
    (stateOrigins : FutureFreeStateHasPathOrigins entryOrigin prior state)
    (snapshotOrigins : RuntimeCoreHasPathOrigins entryOrigin (prior ++ suffix)
      snapshot.core) :
    FutureFreeStateHasPathOrigins entryOrigin (prior ++ suffix)
      (appendFutureFreeSnapshot state event snapshot) := by
  constructor
  · simpa [appendFutureFreeSnapshot] using snapshotOrigins
  · intro transition member
    simp only [appendFutureFreeSnapshot, List.mem_append,
      List.mem_singleton] at member
    rcases member with old | rfl
    · exact runtime_core_has_path_origins_append entryOrigin prior suffix
        transition.before.core (stateOrigins.2 transition old)
    · exact runtime_core_has_path_origins_append entryOrigin prior suffix
        state.current.core stateOrigins.1

/-- One literal future-free microstep preserves operational digest
provenance.  The prover branch has no oracle answers; the verifier branch uses
the exact forced-action query path; stutter changes nothing. -/
theorem future_free_operational_step_preserves_path_origins
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (entryOrigin : Digest256 → Prop)
    (prior stepPairs : List (ShaInput × ShaOutput))
    (state next : FutureFreeVerifierState)
    (origins : FutureFreeStateHasPathOrigins entryOrigin prior state)
    (step : FutureFreeOperationalStep environment raw state stepPairs next) :
    FutureFreeStateHasPathOrigins entryOrigin (prior ++ stepPairs) next := by
  cases step with
  | prover submitted event snapshot appendExact =>
      have nextCore := successful_raw_submission_preserves_runtime_core raw
        state next submitted
      have snapshotCore : snapshot.core = state.current.core := by
        rw [appendExact] at nextCore
        simpa [appendFutureFreeSnapshot] using nextCore
      rw [appendExact]
      apply append_future_free_snapshot_preserves_path_origins entryOrigin
        prior [] state event snapshot origins
      simpa [snapshotCore] using origins.1
  | verifier forced replyPath advanced =>
      obtain ⟨actualAction, nextCore, snapshot, actualForced, coreRun,
          snapshotRun, nextExact⟩ :=
        successful_future_free_advance_has_exact_components environment state
          next _ advanced
      have actionExact := Option.some.inj (actualForced.symm.trans forced)
      cases actionExact
      have nextCoreOrigins :=
        apply_action_work_erased_preserves_path_origins entryOrigin prior
          stepPairs state nextCore _ _ origins.1 replyPath coreRun
      have snapshotCore := after_future_free_reply_has_exact_core environment
        state.current snapshot _ nextCore snapshotRun
      rw [nextExact]
      apply append_future_free_snapshot_preserves_path_origins entryOrigin prior
        stepPairs state _ snapshot origins
      simpa [snapshotCore] using nextCoreOrigins
  | stutter noSubmission noAction =>
      simpa using origins

/-- Chronological closure for an arbitrary operational suffix. -/
theorem future_free_operational_trace_preserves_path_origins
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (entryOrigin : Digest256 → Prop) :
    ∀ {initial final : FutureFreeVerifierState}
      {pairs : List (ShaInput × ShaOutput)},
      FutureFreeOperationalTrace environment raw initial pairs final →
      ∀ prior,
        FutureFreeStateHasPathOrigins entryOrigin prior initial →
        FutureFreeStateHasPathOrigins entryOrigin (prior ++ pairs) final := by
  intro initial final pairs trace
  induction trace with
  | stop state =>
      intro prior origins
      simpa using origins
  | @next state middle final head tail step rest ih =>
      intro prior origins
      have middleOrigins :=
        future_free_operational_step_preserves_path_origins environment raw
          entryOrigin prior head state middle origins step
      have finalOrigins := ih (prior ++ head) middleOrigins
      simpa [List.append_assoc] using finalOrigins

/-- Restored states contain no stale transition suffix.  Therefore a concrete
entry-core predicate immediately initializes the operational provenance
induction, including the saved q16 base needed by later restore actions. -/
theorem restored_state_initializes_path_origins
    (entryOrigin : Digest256 → Prop) (state : FutureFreeVerifierState)
    (noTransitions : state.transitions = [])
    (coreOrigins : RuntimeCoreHasPathOrigins entryOrigin [] state.current.core) :
    FutureFreeStateHasPathOrigins entryOrigin [] state := by
  refine ⟨coreOrigins, ?_⟩
  intro transition member
  rw [noTransitions] at member
  simp at member

#print axioms future_free_reply_path_contains_every_reply_answer
#print axioms apply_action_work_erased_core_sources
#print axioms apply_action_work_erased_preserves_path_origins
#print axioms successful_raw_submission_preserves_runtime_core
#print axioms future_free_operational_step_preserves_path_origins
#print axioms future_free_operational_trace_preserves_path_origins
#print axioms restored_state_initializes_path_origins

end

end AspisK1.V7Tag73FutureFreeGlobalDigestProvenance
