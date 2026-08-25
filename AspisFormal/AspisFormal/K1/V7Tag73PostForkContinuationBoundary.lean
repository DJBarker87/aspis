import AspisFormal.K1.V7Tag73ConcreteKnowledgeInsertion
import AspisFormal.K1.V7Tag73ExecutableHistoryMatcher

/-!
# Exact post-fork replay pairing and continuation boundary

A successful origin-restricted replay can be paired with the unique complete
Tag-73 state at one generated driving query.  The verifier side of that pair
has one atomic two-query squeeze: `H(S || 0x01)` and `H(S || 0x02)` at the
same saved state.

The generic `SameTapeBlackBox` does not, however, require its adversary
continuation to issue the advance query after receiving a changed output.
The final section gives a kernel-checked counterexample.  Consequently the
adaptive lazy-oracle proof must derive that query from fresh acceptance outside
an explicit prediction/collision event; it cannot obtain it from same-tape
restart alone.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PostForkContinuationBoundary

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73ConcreteStateRestoration
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73ExecutableHistoryMatcher
open AspisK1.V7Tag73ConcreteKnowledgeInsertion

noncomputable section

/-! ## One actually constructed replay at a generated checkpoint -/

/-- All data in this object are operational sources.  The origin is computed
from one hidden tape, the replay is returned by
`constructLegalReplayFromOrigin?`, and the restored verifier state below is a
definition from `execution` and `generated`, not a structure field. -/
structure ConcreteGeneratedPostForkReplay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution
      (fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt)
      dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : OriginReplayConfiguration) where
  output :
    {run : CoupledReplay TapeIdentity Statement Proof Result //
      IsOperationalCoupling source.origin.capability
        (fixedFirstRunRecordFromOrigin source.origin
          (configurationForGeneratedReplay execution generated configuration))
        run}
  constructed :
    constructLegalReplayFromOrigin? source.origin
      (configurationForGeneratedReplay execution generated configuration) =
        some output

def ConcreteGeneratedPostForkReplay.replay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution
      (fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt)
      dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : OriginReplayConfiguration}
    (fork : ConcreteGeneratedPostForkReplay source execution generated
      configuration) : CoupledReplay TapeIdentity Statement Proof Result :=
  fork.output.1

def ConcreteGeneratedPostForkReplay.restoration
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution
      (fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt)
      dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : OriginReplayConfiguration}
    (_fork : ConcreteGeneratedPostForkReplay source execution generated
      configuration) : ConcreteRestorationRecord
        (fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt)
        dag :=
  concreteRestoration execution generated

noncomputable def ConcreteGeneratedPostForkReplay.outputInput
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution
      (fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt)
      dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : OriginReplayConfiguration}
    (fork : ConcreteGeneratedPostForkReplay source execution generated
      configuration) : ShaInput :=
  bytes fork.restoration.snapshot.core.digest ++ [domSqueeze]

noncomputable def ConcreteGeneratedPostForkReplay.advanceInput
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution
      (fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt)
      dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : OriginReplayConfiguration}
    (fork : ConcreteGeneratedPostForkReplay source execution generated
      configuration) : ShaInput :=
  bytes fork.restoration.snapshot.core.digest ++ [domAdvance]

/-- The strongest unconditional pairing currently available.  It identifies
the actual replay pause with the generated squeeze-output input and proves the
complete verifier side expects one atomic output/advance pair at that exact
state.  It deliberately makes no claim that the adversary's changed
continuation issued the advance query. -/
theorem constructed_replay_pairs_with_exact_complete_atomic_squeeze
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution
      (fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt)
      dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : OriginReplayConfiguration}
    (fork : ConcreteGeneratedPostForkReplay source execution generated
      configuration) :
    let restoration := fork.restoration
    fork.replay.driving.input = fork.outputInput ∧
      (fullPlan dag.tape).get restoration.actionCursor =
        .squeezePair restoration.checkpoint.owner
          restoration.checkpoint.block ∧
      actionInputs restoration.snapshot.bindings restoration.snapshot.core
          (.squeezePair restoration.checkpoint.owner
            restoration.checkpoint.block) =
        [fork.outputInput, fork.advanceInput] ∧
      fork.outputInput ≠ fork.advanceInput ∧
      IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot execution.interactiveState ∧
      NonemptyVerifierHistory execution.interactiveState ∧
      restoration.snapshot.bindings =
        FixedBindings.ofContext dag.tape.messages.context ∧
      restoration.oracleTable =
        fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt ∧
      restoration.deployedTape = dag.tape ∧
      fork.replay.tapeIdentity = source.origin.firstRun.tapeIdentity ∧
      source.origin.capability.start source.observation =
        source.blackBox.start source.hiddenTape source.observation := by
  have paired :=
    successful_generated_replay_pairs_with_unique_complete_restoration
      source.origin execution generated configuration fork.output
        fork.constructed
  let restoration := fork.restoration
  have atomic :=
    restoration_squeeze_is_one_atomic_two_query_action restoration
  have operational :=
    map_from_origin_success_preserves_identity_q1_pause_history_resources
      source.origin
      (configurationForGeneratedReplay execution generated configuration)
      fork.output fork.constructed
  refine ⟨?_, atomic.1, ?_, ?_, paired.2.2.1,
    paired.2.2.2.1, paired.2.2.2.2.1,
    paired.2.2.2.2.2.1, paired.2.2.2.2.2.2.1,
    paired.2.2.2.2.2.2.2.1, operational.2.1,
    source_origin_capability_uses_same_hidden_tape source⟩
  · simpa [ConcreteGeneratedPostForkReplay.replay,
      ConcreteGeneratedPostForkReplay.outputInput,
      ConcreteGeneratedPostForkReplay.restoration,
      generatedDrivingInput] using paired.1
  · change actionInputs restoration.snapshot.bindings
        restoration.snapshot.core
          (.squeezePair restoration.checkpoint.owner
            restoration.checkpoint.block) =
        [bytes restoration.snapshot.core.digest ++ [domSqueeze],
         bytes restoration.snapshot.core.digest ++ [domAdvance]]
    simpa only [domSqueeze, domAdvance] using atomic.2.1
  · change bytes restoration.snapshot.core.digest ++ [domSqueeze] ≠
      bytes restoration.snapshot.core.digest ++ [domAdvance]
    exact squeeze_output_and_advance_inputs_are_distinct
      restoration.snapshot.core.digest

/-! ## Optional executable ordered-history check -/

noncomputable def ConcreteGeneratedPostForkReplay.historyMatches
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution
      (fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt)
      dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : OriginReplayConfiguration}
    (fork : ConcreteGeneratedPostForkReplay source execution generated
      configuration) : Bool :=
  coupledReplayMatchesGenerated execution generated fork.replay

theorem history_match_exposes_exact_generated_prefix
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution
      (fixedTableOfOracleState source.origin.firstRun.stateAtAdversaryHalt)
      dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : OriginReplayConfiguration}
    (fork : ConcreteGeneratedPostForkReplay source execution generated
      configuration)
    (matched : fork.historyMatches = true) :
    List.Sublist (expectedGeneratedQueryAnswerPrefix execution generated)
        (queryAnswerTrace fork.replay.replayPrefix) ∧
      fork.replay.driving.input = generatedDrivingInput execution generated := by
  exact coupled_replay_match_success_exposes_exact_schedule_and_pause
    execution generated fork.replay matched

/-! ## Smallest exact insufficiency of the generic black box -/

/-- Query-shape predicate for one next oracle call. -/
def QueriesNext {Result : Type*}
    (program : OracleMachine Result) (input : ShaInput) : Prop :=
  match program with
  | .query actual _ => actual = input
  | .pure _ | .abort _ => False

/-- The adversary program itself issues both halves in order for every
possible changed output.  This is stronger than the verifier-side atomic
action proved above. -/
def HasAtomicOutputAdvanceContinuation {Result : Type*}
    (program : OracleMachine Result) (outputInput advanceInput : ShaInput) :
    Prop :=
  match program with
  | .query actual next =>
      actual = outputInput ∧ ∀ output, QueriesNext (next output) advanceInput
  | .pure _ | .abort _ => False

/-- A legal same-tape black box can stop immediately after the exact output
query.  It therefore satisfies the output-query half but not the advance-query
half, for every choice of inputs. -/
def outputOnlySameTapeBlackBox (outputInput : ShaInput) :
    SameTapeBlackBox Unit Unit Unit where
  start _ _ := .query outputInput fun _ => .pure ()

@[simp] theorem output_only_black_box_queries_exact_output
    (outputInput : ShaInput) :
    QueriesNext ((outputOnlySameTapeBlackBox outputInput).start () ())
      outputInput := by
  rfl

@[simp] theorem output_only_black_box_has_no_atomic_advance
    (outputInput advanceInput : ShaInput) :
    ¬ HasAtomicOutputAdvanceContinuation
      ((outputOnlySameTapeBlackBox outputInput).start () ())
      outputInput advanceInput := by
  simp [HasAtomicOutputAdvanceContinuation, QueriesNext,
    outputOnlySameTapeBlackBox]

/-- Kernel-checked obstruction: even a capability produced by
`closeSameTapeStart` over one fixed hidden tape and beginning at the exact
driving query need not issue the paired advance query.  Thus no theorem with
that conclusion follows from `SameTapeBlackBox` alone. -/
theorem same_tape_start_is_insufficient_for_atomic_advance
    (outputInput advanceInput : ShaInput) :
    ∃ blackBox : SameTapeBlackBox Unit Unit Unit,
      let capability := closeSameTapeStart blackBox () ()
      QueriesNext (capability.start ()) outputInput ∧
        ¬ HasAtomicOutputAdvanceContinuation (capability.start ())
          outputInput advanceInput := by
  refine ⟨outputOnlySameTapeBlackBox outputInput, ?_⟩
  exact ⟨output_only_black_box_queries_exact_output outputInput,
    output_only_black_box_has_no_atomic_advance outputInput advanceInput⟩

/-- The operational predicate also intentionally does not mention the
bookkeeping field `programmedOutput`; changing only that field preserves every
currently stated operational invariant.  Construction fixes the field, but
the predicate alone cannot be used to recover it. -/
theorem operational_coupling_does_not_constrain_programmed_output
    {RandomTape Observation Statement Proof Result : Type*}
    (capability : SameTapeStartCapability RandomTape Observation Result)
    (record : FixedFirstRunRecord RandomTape Observation Statement Proof Result)
    (replay : CoupledReplay RandomTape Statement Proof Result)
    (operational : IsOperationalCoupling capability record replay)
    (replacement : ShaOutput) :
    IsOperationalCoupling capability record
      { replay with programmedOutput := replacement } := by
  exact operational

#print axioms constructed_replay_pairs_with_exact_complete_atomic_squeeze
#print axioms history_match_exposes_exact_generated_prefix
#print axioms output_only_black_box_queries_exact_output
#print axioms output_only_black_box_has_no_atomic_advance
#print axioms same_tape_start_is_insufficient_for_atomic_advance
#print axioms operational_coupling_does_not_constrain_programmed_output

end

end AspisK1.V7Tag73PostForkContinuationBoundary
