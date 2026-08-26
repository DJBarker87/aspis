import AspisFormal.K1.V7Tag73RawSameTapeSource
import AspisFormal.K1.V7Tag73SharedOracleVerifierRunner
import AspisFormal.K1.V7Tag73ReturnedPlanSemantics

/-!
# Oracle-driven future-free Tag-73 verifier

This is the operational bridge between one raw prover return and the
future-free interactive state machine.  Prover-owned transitions are supplied
from `RawTag73ProverMessages`; verifier transitions issue the exact SHA inputs
computed by the current live state.  A squeeze is one program containing the
two distinct sequential queries `S || 01` and `S || 02`.

The driver is fuel bounded and returns a verifier state, not an acceptance or
witness.  Semantic, two-tree and terminal acceptance remain the explicit
K1.2--K1.5 layer.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawFutureFreeDriver

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73ReturnedPlanSemantics
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement

/-! ## Complete previously-seen future-free histories -/

/-- Structural closure of the explicit verifier history.  This property says
that restoration candidates are actual snapshots in one nonempty execution;
it contains no acceptance or extraction conclusion. -/
def FutureFreeHistoryClosed (state : FutureFreeVerifierState) : Prop :=
  state.seen ≠ [] ∧
    state.current ∈ state.seen ∧
    ∀ transition ∈ state.transitions,
      transition.before ∈ state.seen ∧
        transition.after ∈ state.seen

/-- All complete snapshots in one run carry the one raw public instance.
This includes potential restoration targets, not only the final state. -/
def FutureFreeBindingsFixed (bindings : FixedBindings)
    (state : FutureFreeVerifierState) : Prop :=
  state.current.bindings = bindings ∧
    ∀ snapshot ∈ state.seen, snapshot.bindings = bindings

def FutureFreeRunInvariant (bindings : FixedBindings)
    (state : FutureFreeVerifierState) : Prop :=
  FutureFreeHistoryClosed state ∧ FutureFreeBindingsFixed bindings state

theorem initial_future_free_history_is_closed (bindings : FixedBindings) :
    FutureFreeHistoryClosed (initialFutureFreeVerifierState bindings) := by
  simp [FutureFreeHistoryClosed, initialFutureFreeVerifierState]

theorem initial_future_free_bindings_are_fixed (bindings : FixedBindings) :
    FutureFreeBindingsFixed bindings
      (initialFutureFreeVerifierState bindings) := by
  simp [FutureFreeBindingsFixed, initialFutureFreeVerifierState,
    initialFutureFreeSnapshot]

theorem initial_future_free_run_invariant (bindings : FixedBindings) :
    FutureFreeRunInvariant bindings
      (initialFutureFreeVerifierState bindings) := by
  exact ⟨initial_future_free_history_is_closed bindings,
    initial_future_free_bindings_are_fixed bindings⟩

theorem append_future_free_snapshot_preserves_history_closed
    (state : FutureFreeVerifierState) (event : FutureFreeEvent)
    (next : FutureFreeSnapshot)
    (closed : FutureFreeHistoryClosed state) :
    FutureFreeHistoryClosed (appendFutureFreeSnapshot state event next) := by
  rcases closed with ⟨nonempty, currentSeen, transitionsSeen⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [appendFutureFreeSnapshot]
  · simp [appendFutureFreeSnapshot]
  · intro transition member
    simp only [appendFutureFreeSnapshot, List.mem_append,
      List.mem_singleton] at member ⊢
    rcases member with old | rfl
    · obtain ⟨beforeSeen, afterSeen⟩ := transitionsSeen transition old
      exact ⟨Or.inl beforeSeen, Or.inl afterSeen⟩
    · exact ⟨Or.inl currentSeen, Or.inr rfl⟩

theorem append_future_free_snapshot_preserves_fixed_bindings
    (bindings : FixedBindings) (state : FutureFreeVerifierState)
    (event : FutureFreeEvent) (next : FutureFreeSnapshot)
    (fixed : FutureFreeBindingsFixed bindings state)
    (nextFixed : next.bindings = bindings) :
    FutureFreeBindingsFixed bindings
      (appendFutureFreeSnapshot state event next) := by
  rcases fixed with ⟨currentFixed, seenFixed⟩
  refine ⟨nextFixed, ?_⟩
  intro snapshot member
  simp only [appendFutureFreeSnapshot, List.mem_append,
    List.mem_singleton] at member
  rcases member with old | rfl
  · exact seenFixed snapshot old
  · exact nextFixed

/-! Every executable prover transition and verifier transition below is a
literal `appendFutureFreeSnapshot`.  These lemmas make that fact available to
the recursive driver, so a future restoration point never has to be supplied
by a caller. -/

theorem submit_future_free_c1_preserves_history_closed
    (state next : FutureFreeVerifierState)
    (root : TypedMerkleRoot .initialC1)
    (closed : FutureFreeHistoryClosed state)
    (submitted : submitFutureFreeC1 state root = some next) :
    FutureFreeHistoryClosed next := by
  unfold submitFutureFreeC1 at submitted
  split at submitted
  next controlEq =>
    have nextEq := Option.some.inj submitted
    rw [← nextEq]
    exact append_future_free_snapshot_preserves_history_closed _ _ _ closed
  all_goals simp at submitted

theorem submit_future_free_c2_preserves_history_closed
    (state : FutureFreeVerifierState) (lambda chi : Qm31Bytes)
    (commitment : C2Commitment lambda chi)
    (atC2 : state.current.control =
      .adaptive (.awaitingC2 lambda chi))
    (closed : FutureFreeHistoryClosed state) :
    FutureFreeHistoryClosed
      (submitFutureFreeC2 state lambda chi commitment atC2) := by
  unfold submitFutureFreeC2
  exact append_future_free_snapshot_preserves_history_closed _ _ _ closed

theorem submit_future_free_payload_preserves_history_closed
    (state next : FutureFreeVerifierState) (payload : Payload)
    (closed : FutureFreeHistoryClosed state)
    (submitted : submitFutureFreePayload state payload = some next) :
    FutureFreeHistoryClosed next := by
  unfold submitFutureFreePayload at submitted
  split at submitted
  next site remaining controlEq =>
    split at submitted
    next matched =>
      have nextEq := Option.some.inj submitted
      rw [← nextEq]
      exact append_future_free_snapshot_preserves_history_closed _ _ _ closed
    next => simp at submitted
  all_goals simp at submitted

theorem submit_future_free_work_preserves_history_closed
    (state next : FutureFreeVerifierState) (nonce : NonceBytes)
    (closed : FutureFreeHistoryClosed state)
    (submitted : submitFutureFreeWorkNonce state nonce = some next) :
    FutureFreeHistoryClosed next := by
  unfold submitFutureFreeWorkNonce at submitted
  split at submitted
  next stage remaining controlEq =>
    have nextEq := Option.some.inj submitted
    rw [← nextEq]
    exact append_future_free_snapshot_preserves_history_closed _ _ _ closed
  all_goals simp at submitted

theorem advance_future_free_verifier_preserves_history_closed
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (closed : FutureFreeHistoryClosed state)
    (advanced : advanceFutureFreeVerifier environment state reply = some next) :
    FutureFreeHistoryClosed next := by
  rw [advanceFutureFreeVerifier] at advanced
  obtain ⟨action, _actionEq, advanced⟩ := Option.bind_eq_some_iff.mp advanced
  obtain ⟨nextCore, _coreEq, advanced⟩ :=
    Option.bind_eq_some_iff.mp advanced
  obtain ⟨nextSnapshot, _snapshotEq, finalEq⟩ :=
    Option.bind_eq_some_iff.mp advanced
  have nextEq : appendFutureFreeSnapshot state
      (.verifier action reply) nextSnapshot = next := Option.some.inj finalEq
  rw [← nextEq]
  exact append_future_free_snapshot_preserves_history_closed _ _ _ closed

theorem successful_future_free_advance_is_complete_append
    (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (advanced : advanceFutureFreeVerifier environment state reply = some next) :
    ∃ action snapshot,
      next = appendFutureFreeSnapshot state (.verifier action reply) snapshot := by
  rw [advanceFutureFreeVerifier] at advanced
  obtain ⟨action, _actionEq, advanced⟩ := Option.bind_eq_some_iff.mp advanced
  obtain ⟨nextCore, _coreEq, advanced⟩ :=
    Option.bind_eq_some_iff.mp advanced
  obtain ⟨nextSnapshot, _snapshotEq, finalEq⟩ :=
    Option.bind_eq_some_iff.mp advanced
  exact ⟨action, nextSnapshot, (Option.some.inj finalEq).symm⟩

theorem submit_next_raw_message_preserves_fixed_bindings
    (bindings : FixedBindings) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (fixed : FutureFreeBindingsFixed bindings state)
    (submitted : submitNextRawMessage raw state = some next) :
    FutureFreeBindingsFixed bindings next := by
  obtain ⟨event, snapshot, nextEq⟩ :=
    successful_raw_submission_is_complete_append raw state next submitted
  have currentFixed : state.current.bindings = bindings := fixed.1
  have submittedFixed : next.current.bindings = state.current.bindings :=
    successful_raw_submission_preserves_bindings raw state next submitted
  rw [nextEq] at submittedFixed ⊢
  apply append_future_free_snapshot_preserves_fixed_bindings bindings state
    event snapshot fixed
  simpa [appendFutureFreeSnapshot] using submittedFixed.trans currentFixed

theorem advance_future_free_verifier_preserves_fixed_bindings
    (bindings : FixedBindings) (environment : FutureFreeEnvironment)
    (state next : FutureFreeVerifierState) (reply : VerifierReply)
    (fixed : FutureFreeBindingsFixed bindings state)
    (advanced : advanceFutureFreeVerifier environment state reply = some next) :
    FutureFreeBindingsFixed bindings next := by
  obtain ⟨action, snapshot, nextEq⟩ :=
    successful_future_free_advance_is_complete_append environment state next
      reply advanced
  have currentFixed : state.current.bindings = bindings := fixed.1
  have advancedFixed : next.current.bindings = state.current.bindings :=
    successful_future_free_advance_preserves_bindings environment state next
      reply advanced
  rw [nextEq] at advancedFixed ⊢
  apply append_future_free_snapshot_preserves_fixed_bindings bindings state
    (.verifier action reply) snapshot fixed
  simpa [appendFutureFreeSnapshot] using advancedFixed.trans currentFixed

/-! ## One exact verifier action as an oracle program -/

def structuralFutureFreeReply : VerifierAction → Option VerifierReply
  | .checkpoint _ | .markQ16Base | .q16Restore _ | .q16Selected _ |
      .q16SamplerAbortReject _ | .q16AllNoncompactReject | .terminal =>
        some .none
  | _ => none

def futureFreeReplyProgram (state : FutureFreeVerifierState)
    (action : VerifierAction) : OracleMachine VerifierReply :=
  match structuralFutureFreeReply action with
  | some reply => .pure reply
  | none =>
      match action with
      | .squeezePair _ _ =>
          let outputInput := bytes state.current.core.digest ++ [domSqueeze]
          let advanceInput := bytes state.current.core.digest ++ [domAdvance]
          .query outputInput fun output =>
            .query advanceInput fun advance =>
              .pure (.squeeze output advance)
      | _ =>
          match actionInputs state.current.bindings state.current.core action with
          | [input] => .query input fun output => .pure (.single output)
          | _ => .abort .controllerRefused

theorem future_free_squeeze_program_is_exact_atomic_pair
    (state : FutureFreeVerifierState) (owner : SqueezeOwner) (block : Nat) :
    futureFreeReplyProgram state (.squeezePair owner block) =
      .query (bytes state.current.core.digest ++ [domSqueeze]) fun output =>
        .query (bytes state.current.core.digest ++ [domAdvance]) fun advance =>
          .pure (.squeeze output advance) := by
  rfl

theorem future_free_squeeze_inputs_are_distinct
    (state : FutureFreeVerifierState) :
    bytes state.current.core.digest ++ [domSqueeze] ≠
      bytes state.current.core.digest ++ [domAdvance] :=
  squeeze_output_and_advance_inputs_are_distinct state.current.core.digest

def runOneFutureFreeVerifierAction (environment : FutureFreeEnvironment)
    (state : FutureFreeVerifierState) : OracleMachine FutureFreeVerifierState :=
  match actionFound : state.current.control.nextVerifierAction? with
  | none => .pure state
  | some action =>
      bindOracleMachine (futureFreeReplyProgram state action) fun reply =>
        match advanceFutureFreeVerifier environment state reply with
        | some next => .pure next
        | none => .abort .controllerRefused

/-! ## Interleave exact raw submissions with verifier actions -/

def isDriverHalt : FutureFreeControl → Bool
  | .done => true
  | .rejected _ => true
  | .adaptive .rejected => true
  | _ => false

/-- One driver microstep.  A pending prover field has priority exactly because
the verifier has no legal action in those states.  Otherwise the next action
is forced by `FutureFreeControl.nextVerifierAction?`. -/
def rawFutureFreeMicrostep (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState) :
    OracleMachine FutureFreeVerifierState :=
  match submitNextRawMessage raw state with
  | some next => .pure next
  | none => runOneFutureFreeVerifierAction environment state

/-- Fuel bounds zero-query prover transitions as well as oracle-driven
verifier transitions.  Resource accounting later separates oracle calls from
this transition fuel. -/
def driveRawFutureFree (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) : Nat → FutureFreeVerifierState →
      OracleMachine FutureFreeVerifierState
  | 0, state => .pure state
  | fuel + 1, state =>
      bindOracleMachine (rawFutureFreeMicrostep environment raw state) fun next =>
        if terminal : isDriverHalt next.current.control then
          .pure next
        else
          driveRawFutureFree environment raw fuel next

def initialRawFutureFreeProgram (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (fuel : Nat) :
    OracleMachine FutureFreeVerifierState :=
  driveRawFutureFree environment raw fuel
    (initialFutureFreeVerifierState (FixedBindings.ofContext raw.context))

/-! ## Operational step and trace certificates -/

/-- One actual driver step.  The prover constructor stores the append shape
derived from `submitNextRawMessage`; the verifier constructor stores the
literal query path through the forced action.  `stutter` is possible only
when neither a raw submission nor a verifier action is available. -/
inductive FutureFreeOperationalStep
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    FutureFreeVerifierState → List (ShaInput × ShaOutput) →
      FutureFreeVerifierState → Prop where
  | prover {state next : FutureFreeVerifierState}
      (submitted : submitNextRawMessage raw state = some next)
      (event : FutureFreeEvent) (snapshot : FutureFreeSnapshot)
      (appendExact : next = appendFutureFreeSnapshot state event snapshot) :
      FutureFreeOperationalStep environment raw state [] next
  | verifier {state next : FutureFreeVerifierState}
      {action : VerifierAction} {reply : VerifierReply}
      {pairs : List (ShaInput × ShaOutput)}
      (forced : state.current.control.nextVerifierAction? = some action)
      (replyPath : MachineQueryPath
        (futureFreeReplyProgram state action) pairs reply)
      (advanced : advanceFutureFreeVerifier environment state reply = some next) :
      FutureFreeOperationalStep environment raw state pairs next
  | stutter {state : FutureFreeVerifierState}
      (noSubmission : submitNextRawMessage raw state = none)
      (noAction : state.current.control.nextVerifierAction? = none) :
      FutureFreeOperationalStep environment raw state [] state

/-- Finite chronological sequence of actual operational steps. -/
inductive FutureFreeOperationalTrace
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    FutureFreeVerifierState → List (ShaInput × ShaOutput) →
      FutureFreeVerifierState → Prop where
  | stop (state : FutureFreeVerifierState) :
      FutureFreeOperationalTrace environment raw state [] state
  | next {state middle final : FutureFreeVerifierState}
      {head tail : List (ShaInput × ShaOutput)}
      (step : FutureFreeOperationalStep environment raw state head middle)
      (rest : FutureFreeOperationalTrace environment raw middle tail final) :
      FutureFreeOperationalTrace environment raw state (head ++ tail) final

theorem initial_raw_future_free_program_has_nonempty_dummy_state
    (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (fuel : Nat) :
    let initial :=
      initialFutureFreeVerifierState (FixedBindings.ofContext raw.context)
    initial.seen ≠ [] ∧
      initialRawFutureFreeProgram environment raw 0 = .pure initial := by
  exact ⟨initial_future_free_history_is_nonempty _, rfl⟩

/-! ## Closure of every actual returned driver path -/

theorem submit_next_raw_message_preserves_history_closed
    (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (closed : FutureFreeHistoryClosed state)
    (submitted : submitNextRawMessage raw state = some next) :
    FutureFreeHistoryClosed next := by
  unfold submitNextRawMessage at submitted
  split at submitted
  next controlEq =>
    exact submit_future_free_c1_preserves_history_closed state next
      (rawC1Root raw) closed submitted
  next lambda chi controlEq =>
    have nextEq : submitFutureFreeC2 state lambda chi
        (raw.c2Commitment lambda chi) controlEq = next :=
      Option.some.inj submitted
    rw [← nextEq]
    exact submit_future_free_c2_preserves_history_closed state lambda chi
      (raw.c2Commitment lambda chi) controlEq closed
  next site remaining controlEq =>
    exact submit_future_free_payload_preserves_history_closed state next
      (rawPayloadAt raw site) closed submitted
  next stage remaining controlEq =>
    exact submit_future_free_work_preserves_history_closed state next
      (rawWorkNonceAt raw stage) closed submitted
  all_goals simp at submitted

theorem run_one_future_free_verifier_action_path_preserves_history_closed
    (environment : FutureFreeEnvironment)
    (state result : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (closed : FutureFreeHistoryClosed state)
    (path : MachineQueryPath
      (runOneFutureFreeVerifierAction environment state) pairs result) :
    FutureFreeHistoryClosed result := by
  unfold runOneFutureFreeVerifierAction at path
  split at path
  next actionFound =>
    cases path
    exact closed
  next action actionFound =>
    obtain ⟨reply, headPairs, tailPairs, _replyPath, tailPath, _pairsEq⟩ :=
      machine_query_path_bind_split
        (futureFreeReplyProgram state action)
        (fun reply =>
          match advanceFutureFreeVerifier environment state reply with
          | some next => .pure next
          | none => .abort .controllerRefused)
        pairs result path
    cases advanced : advanceFutureFreeVerifier environment state reply with
    | none =>
        simp [advanced] at tailPath
        cases tailPath
    | some next =>
        have nextClosed := advance_future_free_verifier_preserves_history_closed
          environment state next reply closed advanced
        simp [advanced] at tailPath
        cases tailPath
        exact nextClosed

theorem raw_future_free_microstep_path_preserves_history_closed
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state result : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (closed : FutureFreeHistoryClosed state)
    (path : MachineQueryPath
      (rawFutureFreeMicrostep environment raw state) pairs result) :
    FutureFreeHistoryClosed result := by
  unfold rawFutureFreeMicrostep at path
  split at path
  next next submitted =>
    have nextClosed := submit_next_raw_message_preserves_history_closed raw
      state next closed submitted
    cases path
    exact nextClosed
  next missing =>
    exact run_one_future_free_verifier_action_path_preserves_history_closed
      environment state result pairs closed path

theorem drive_raw_future_free_path_preserves_history_closed
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    ∀ fuel state pairs result,
      FutureFreeHistoryClosed state →
      MachineQueryPath (driveRawFutureFree environment raw fuel state)
        pairs result →
      FutureFreeHistoryClosed result := by
  intro fuel
  induction fuel with
  | zero =>
      intro state pairs result closed path
      cases path
      exact closed
  | succ fuel ih =>
      intro state pairs result closed path
      simp only [driveRawFutureFree] at path
      obtain ⟨next, headPairs, tailPairs, headPath, tailPath, _pairsEq⟩ :=
        machine_query_path_bind_split
          (rawFutureFreeMicrostep environment raw state)
          (fun next =>
            if isDriverHalt next.current.control then .pure next
            else driveRawFutureFree environment raw fuel next)
          pairs result path
      have nextClosed :=
        raw_future_free_microstep_path_preserves_history_closed environment raw
          state next headPairs closed headPath
      by_cases terminal : isDriverHalt next.current.control
      · simp [terminal] at tailPath
        cases tailPath
        exact nextClosed
      · simp [terminal] at tailPath
        exact ih next tailPairs result nextClosed tailPath

theorem initial_raw_future_free_return_has_closed_nonempty_seen_history
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (pairs : List (ShaInput × ShaOutput))
    (result : FutureFreeVerifierState)
    (path : MachineQueryPath
      (initialRawFutureFreeProgram environment raw fuel) pairs result) :
    FutureFreeHistoryClosed result := by
  exact drive_raw_future_free_path_preserves_history_closed environment raw fuel
    (initialFutureFreeVerifierState (FixedBindings.ofContext raw.context))
    pairs result (initial_future_free_history_is_closed _) path

theorem run_one_future_free_verifier_action_path_preserves_fixed_bindings
    (bindings : FixedBindings) (environment : FutureFreeEnvironment)
    (state result : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (fixed : FutureFreeBindingsFixed bindings state)
    (path : MachineQueryPath
      (runOneFutureFreeVerifierAction environment state) pairs result) :
    FutureFreeBindingsFixed bindings result := by
  unfold runOneFutureFreeVerifierAction at path
  split at path
  next actionFound =>
    cases path
    exact fixed
  next action actionFound =>
    obtain ⟨reply, headPairs, tailPairs, _replyPath, tailPath, _pairsEq⟩ :=
      machine_query_path_bind_split
        (futureFreeReplyProgram state action)
        (fun reply =>
          match advanceFutureFreeVerifier environment state reply with
          | some next => .pure next
          | none => .abort .controllerRefused)
        pairs result path
    cases advanced : advanceFutureFreeVerifier environment state reply with
    | none =>
        simp [advanced] at tailPath
        cases tailPath
    | some next =>
        have nextFixed :=
          advance_future_free_verifier_preserves_fixed_bindings bindings
            environment state next reply fixed advanced
        simp [advanced] at tailPath
        cases tailPath
        exact nextFixed

theorem raw_future_free_microstep_path_preserves_fixed_bindings
    (bindings : FixedBindings) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages)
    (state result : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (fixed : FutureFreeBindingsFixed bindings state)
    (path : MachineQueryPath
      (rawFutureFreeMicrostep environment raw state) pairs result) :
    FutureFreeBindingsFixed bindings result := by
  unfold rawFutureFreeMicrostep at path
  split at path
  next next submitted =>
    have nextFixed := submit_next_raw_message_preserves_fixed_bindings
      bindings raw state next fixed submitted
    cases path
    exact nextFixed
  next missing =>
    exact
      run_one_future_free_verifier_action_path_preserves_fixed_bindings
        bindings environment state result pairs fixed path

theorem drive_raw_future_free_path_preserves_fixed_bindings
    (bindings : FixedBindings) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) :
    ∀ fuel state pairs result,
      FutureFreeBindingsFixed bindings state →
      MachineQueryPath (driveRawFutureFree environment raw fuel state)
        pairs result →
      FutureFreeBindingsFixed bindings result := by
  intro fuel
  induction fuel with
  | zero =>
      intro state pairs result fixed path
      cases path
      exact fixed
  | succ fuel ih =>
      intro state pairs result fixed path
      simp only [driveRawFutureFree] at path
      obtain ⟨next, headPairs, tailPairs, headPath, tailPath, _pairsEq⟩ :=
        machine_query_path_bind_split
          (rawFutureFreeMicrostep environment raw state)
          (fun next =>
            if isDriverHalt next.current.control then .pure next
            else driveRawFutureFree environment raw fuel next)
          pairs result path
      have nextFixed :=
        raw_future_free_microstep_path_preserves_fixed_bindings bindings
          environment raw state next headPairs fixed headPath
      by_cases terminal : isDriverHalt next.current.control
      · simp [terminal] at tailPath
        cases tailPath
        exact nextFixed
      · simp [terminal] at tailPath
        exact ih next tailPairs result nextFixed tailPath

theorem initial_raw_future_free_return_has_exact_run_invariant
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (pairs : List (ShaInput × ShaOutput))
    (result : FutureFreeVerifierState)
    (path : MachineQueryPath
      (initialRawFutureFreeProgram environment raw fuel) pairs result) :
    FutureFreeRunInvariant (FixedBindings.ofContext raw.context) result := by
  exact ⟨
    initial_raw_future_free_return_has_closed_nonempty_seen_history
      environment raw fuel pairs result path,
    drive_raw_future_free_path_preserves_fixed_bindings
      (FixedBindings.ofContext raw.context) environment raw fuel
      (initialFutureFreeVerifierState (FixedBindings.ofContext raw.context))
      pairs result (initial_future_free_bindings_are_fixed _) path⟩

theorem raw_future_free_microstep_path_is_operational
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state result : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (path : MachineQueryPath
      (rawFutureFreeMicrostep environment raw state) pairs result) :
    FutureFreeOperationalStep environment raw state pairs result := by
  unfold rawFutureFreeMicrostep at path
  split at path
  next next submitted =>
    obtain ⟨event, snapshot, appendExact⟩ :=
      successful_raw_submission_is_complete_append raw state next submitted
    cases path
    exact .prover submitted event snapshot appendExact
  next noSubmission =>
    unfold runOneFutureFreeVerifierAction at path
    split at path
    next noAction =>
      cases path
      exact .stutter noSubmission noAction
    next action forced =>
      obtain ⟨reply, headPairs, tailPairs, replyPath, tailPath, pairsExact⟩ :=
        machine_query_path_bind_split
          (futureFreeReplyProgram state action)
          (fun reply =>
            match advanceFutureFreeVerifier environment state reply with
            | some next => .pure next
            | none => .abort .controllerRefused)
          pairs result path
      cases advanced : advanceFutureFreeVerifier environment state reply with
      | none =>
          simp [advanced] at tailPath
          cases tailPath
      | some next =>
          simp [advanced] at tailPath
          cases tailPath
          simp only [List.append_nil] at pairsExact
          subst pairs
          exact .verifier forced replyPath advanced

theorem drive_raw_future_free_path_is_operational_trace
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    ∀ fuel state pairs result,
      MachineQueryPath (driveRawFutureFree environment raw fuel state)
        pairs result →
      FutureFreeOperationalTrace environment raw state pairs result := by
  intro fuel
  induction fuel with
  | zero =>
      intro state pairs result path
      cases path
      exact .stop state
  | succ fuel ih =>
      intro state pairs result path
      simp only [driveRawFutureFree] at path
      obtain ⟨next, headPairs, tailPairs, headPath, tailPath, pairsExact⟩ :=
        machine_query_path_bind_split
          (rawFutureFreeMicrostep environment raw state)
          (fun next =>
            if isDriverHalt next.current.control then .pure next
            else driveRawFutureFree environment raw fuel next)
          pairs result path
      have step := raw_future_free_microstep_path_is_operational environment raw
        state next headPairs headPath
      rw [pairsExact]
      by_cases terminal : isDriverHalt next.current.control
      · simp [terminal] at tailPath
        cases tailPath
        exact .next step (.stop result)
      · simp [terminal] at tailPath
        exact .next step (ih next tailPairs result tailPath)

theorem initial_raw_future_free_path_is_operational_trace
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (fuel : Nat) (pairs : List (ShaInput × ShaOutput))
    (result : FutureFreeVerifierState)
    (path : MachineQueryPath
      (initialRawFutureFreeProgram environment raw fuel) pairs result) :
    FutureFreeOperationalTrace environment raw
      (initialFutureFreeVerifierState (FixedBindings.ofContext raw.context))
      pairs result :=
  drive_raw_future_free_path_is_operational_trace environment raw fuel
    (initialFutureFreeVerifierState (FixedBindings.ofContext raw.context))
    pairs result path

/-- An operational step either inherits an old transition, or its target
history is exactly the old history plus the selected transition. -/
theorem operational_step_transition_is_old_or_new
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (step : FutureFreeOperationalStep environment raw state pairs next)
    (transition : FutureFreeTransition)
    (member : transition ∈ next.transitions) :
    transition ∈ state.transitions ∨
      next.transitions = state.transitions ++ [transition] := by
  cases step with
  | prover submitted event snapshot appendExact =>
      rw [appendExact] at member ⊢
      simp only [appendFutureFreeSnapshot, List.mem_append,
        List.mem_singleton] at member
      rcases member with old | rfl
      · exact Or.inl old
      · exact Or.inr rfl
  | verifier forced replyPath advanced =>
      obtain ⟨action, snapshot, nextEq⟩ :=
        successful_future_free_advance_is_complete_append environment state next
          _ advanced
      rw [nextEq] at member ⊢
      simp only [appendFutureFreeSnapshot, List.mem_append,
        List.mem_singleton] at member
      rcases member with old | rfl
      · exact Or.inl old
      · exact Or.inr rfl
  | stutter noSubmission noAction =>
      exact Or.inl member

/-- Every transition after an operational trace is either inherited from its
entry state or was appended by one actual step in that trace. -/
theorem operational_trace_transition_has_actual_step
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (initial final : FutureFreeVerifierState)
    (pairs : List (ShaInput × ShaOutput))
    (trace : FutureFreeOperationalTrace environment raw initial pairs final)
    (transition : FutureFreeTransition)
    (member : transition ∈ final.transitions) :
    transition ∈ initial.transitions ∨
      ∃ before stepPairs after,
        FutureFreeOperationalStep environment raw before stepPairs after ∧
          after.transitions = before.transitions ++ [transition] := by
  induction trace with
  | stop state => exact Or.inl member
  | @next state middle final head tail step rest ih =>
      rcases ih member with inherited | generated
      · rcases operational_step_transition_is_old_or_new environment raw
          state middle head step transition inherited with old | fresh
        · exact Or.inl old
        · exact Or.inr ⟨state, head, middle, step, fresh⟩
      · exact Or.inr generated

/-- The raw initial state has no inherited transition, so every transition in
an actually returned raw verifier path has a concrete generating step. -/
theorem initial_operational_trace_transition_has_actual_step
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (pairs : List (ShaInput × ShaOutput))
    (final : FutureFreeVerifierState)
    (trace : FutureFreeOperationalTrace environment raw
      (initialFutureFreeVerifierState (FixedBindings.ofContext raw.context))
      pairs final)
    (transition : FutureFreeTransition)
    (member : transition ∈ final.transitions) :
    ∃ before stepPairs after,
      FutureFreeOperationalStep environment raw before stepPairs after ∧
        after.transitions = before.transitions ++ [transition] := by
  rcases operational_trace_transition_has_actual_step environment raw _ _ _
      trace transition member with inherited | generated
  · simp [initialFutureFreeVerifierState] at inherited
  · exact generated

#print axioms future_free_squeeze_program_is_exact_atomic_pair
#print axioms future_free_squeeze_inputs_are_distinct
#print axioms initial_future_free_history_is_closed
#print axioms append_future_free_snapshot_preserves_history_closed
#print axioms initial_raw_future_free_program_has_nonempty_dummy_state
#print axioms submit_next_raw_message_preserves_history_closed
#print axioms run_one_future_free_verifier_action_path_preserves_history_closed
#print axioms raw_future_free_microstep_path_preserves_history_closed
#print axioms drive_raw_future_free_path_preserves_history_closed
#print axioms initial_raw_future_free_return_has_closed_nonempty_seen_history
#print axioms run_one_future_free_verifier_action_path_preserves_fixed_bindings
#print axioms raw_future_free_microstep_path_preserves_fixed_bindings
#print axioms drive_raw_future_free_path_preserves_fixed_bindings
#print axioms initial_raw_future_free_return_has_exact_run_invariant
#print axioms raw_future_free_microstep_path_is_operational
#print axioms drive_raw_future_free_path_is_operational_trace
#print axioms initial_raw_future_free_path_is_operational_trace
#print axioms operational_step_transition_is_old_or_new
#print axioms operational_trace_transition_has_actual_step
#print axioms initial_operational_trace_transition_has_actual_step

end AspisK1.V7Tag73RawFutureFreeDriver
