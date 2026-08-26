import AspisFormal.K1.V7Tag73ReplayRootFromVerifier
import AspisFormal.K1.V7Tag73SequentialOracleRuns
import AspisFormal.K1.V7Tag73CumulativeReplayHistory

/-!
# Resume-derived recursive Tag-73 replay nodes

A returned replay child is not a fresh same-tape experiment origin.  In the
atomic branch it is the result of resuming a residual program derived by an
actual prefix execution; in the no-pair branch it is a new start of the
original closed program from an explicitly programmed oracle state.

This module retains that distinction.  A node keeps the immutable original
`Tag73SameTapeSource`, the dispatcher-produced edge, the branch-local entry
program and oracle, its exact replay run and return, the cumulative programming
history, and the concrete verifier execution of the returned proof's own DAG.
No caller may replace the black box, hidden tape, identity, observation, or
return equation.

The node-local continuation can be inverted exactly, but it is only one
segment of a causal replay path.  A later child may request a checkpoint in
an ancestor segment.  More fundamentally, the old interactive snapshot is
indexed by the whole future proof.  The final sections expose this mismatch,
project fixed runs into a future-free verifier state, and state the operational
tail-program type needed for genuine adaptive restoration.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ResumeDerivedReplayNode

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73ConcreteStateRestoration
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73NoPairReplay
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73ReplayBranchDispatcher
open AspisK1.V7Tag73RestrictedReplayForest
open AspisK1.V7Tag73ReplayReturnedVerifier
open AspisK1.V7Tag73ReplayRootFromVerifier
open AspisK1.V7Tag73OperationalKnowledgeInput
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73ReplayWorkEvidenceBridge
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## Programs derived from one immutable hidden-tape start -/

/-- A program is tied to the original hidden-tape closure either
definitionally at start, or by an actual `runPrefix` pause from an already
provenanced parent program.  There is no constructor for an arbitrary
residual program. -/
inductive SameTapeProgramProvenance
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload) :
    OracleMachine (CheckedTag73AdversaryReturnedValue Statement Proof Payload) →
      Prop where
  | start : SameTapeProgramProvenance source
      (source.toSameTapeSource.origin.capability.start
        source.toSameTapeSource.observation)
  | paused
      {parent residual : OracleMachine
        (CheckedTag73AdversaryReturnedValue Statement Proof Payload)}
      (parentProvenance : SameTapeProgramProvenance source parent)
      (controller : AdaptiveController) (limits : OracleLimits)
      (fuel : Nat) (initialOracle : OracleState)
      (paused :
        (runPrefix controller limits .extractorReplay fuel initialOracle
          parent).halt = .paused residual) :
      SameTapeProgramProvenance source residual

/-- The exact branch-local continuation executed by one dispatcher edge. -/
structure ResumeDerivedContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload) where
  entryOracle : OracleState
  entryProgram : OracleMachine
    (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  programProvenance : SameTapeProgramProvenance source entryProgram
  controller : AdaptiveController
  limits : OracleLimits
  fuel : Nat
  run : MachineRun (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  returnedValue : CheckedTag73AdversaryReturnedValue Statement Proof Payload
  exactRun : run = runMachine controller limits .extractorReplay fuel
    entryOracle entryProgram
  normallyReturned : run.halt = .returned returnedValue

def ResumeDerivedContinuation.proverTrace
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (continuation : ResumeDerivedContinuation source) : List QueryRecord :=
  historySince continuation.entryOracle continuation.run.oracle

/-! ## Construct the continuation from the actual dispatcher outcome -/

/-- Both dispatcher branches construct their continuation from the original
root source.  The atomic branch uses only a residual certified by a real
prefix pause.  The no-pair branch uses the original closed start program from
the exact programmed state in `noPairReplay`. -/
def continuationOfRestrictedChild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    ResumeDerivedContinuation root.source :=
  match child.outcome with
  | .atomic output operational =>
      { entryOracle := output.programming.afterBoth
        entryProgram := output.residualProgram
        programProvenance := by
          rcases operational with
            ⟨_tape, _identity, _q1, _occurrence, _split, _beforeFresh,
              _chosenInput, _actor, _pendingChosen, _halfClassification,
              _pendingHalf, _assigned, prefixDefinition, paused,
              _residualQuery, _trace, _freshOutput, _freshAdvance, _distinct,
              _programmingOrder, _programmed, _replayDefinition,
              _pendingQuery, _returned, _initialHistory, _replayHistory,
              _prefixSteps, _replaySteps, _replayFuelBound, _resources,
              _withinBudget⟩
          apply SameTapeProgramProvenance.paused
            (SameTapeProgramProvenance.start (source := root.source))
            (recordedPrefixController
              root.source.toSameTapeSource.origin.initialOracle.history.length
              output.occurrence.before)
            child.configuration.oracleLimits output.occurrence.before.length
            root.source.toSameTapeSource.origin.initialOracle
          have pausedAtSourceOrigin :
              (runPrefix
                (recordedPrefixController
                  root.source.toSameTapeSource.origin.initialOracle.history.length
                  output.occurrence.before)
                child.configuration.oracleLimits .extractorReplay
                output.occurrence.before.length
                root.source.toSameTapeSource.origin.initialOracle
                (root.source.toSameTapeSource.origin.capability.start
                  root.source.toSameTapeSource.observation)).halt =
                .paused output.residualProgram := by
            have prefixDefinition' : output.prefixRun = runPrefix
                (recordedPrefixController
                  root.source.toSameTapeSource.origin.initialOracle.history.length
                  output.occurrence.before)
                child.configuration.oracleLimits .extractorReplay
                output.occurrence.before.length
                root.source.toSameTapeSource.origin.initialOracle
                (root.source.toSameTapeSource.origin.capability.start
                  root.source.toSameTapeSource.observation) := by
              have originObservation :
                  root.source.toSameTapeSource.origin.observation =
                    root.source.toSameTapeSource.observation := rfl
              simpa only [originObservation] using prefixDefinition
            rw [← prefixDefinition']
            exact paused
          exact pausedAtSourceOrigin
        controller := child.configuration.postForkController
        limits := child.configuration.oracleLimits
        fuel := child.configuration.replayFuel
        run := output.replayRun
        returnedValue := output.returned
        exactRun := by
          rcases operational with
            ⟨_tape, _identity, _q1, _occurrence, _split, _beforeFresh,
              _chosenInput, _actor, _pendingChosen, _halfClassification,
              _pendingHalf, _assigned, _prefixDefinition, _paused,
              residualQuery, _trace, _freshOutput, _freshAdvance, _distinct,
              _programmingOrder, _programmed, replayDefinition,
              _pendingQuery, _returned, _initialHistory, _replayHistory,
              _prefixSteps, _replaySteps, _replayFuelBound, _resources,
              _withinBudget⟩
          rw [residualQuery]
          exact replayDefinition
        normallyReturned := by
          rcases operational with
            ⟨_tape, _identity, _q1, _occurrence, _split, _beforeFresh,
              _chosenInput, _actor, _pendingChosen, _halfClassification,
              _pendingHalf, _assigned, _prefixDefinition, _paused,
              _residualQuery, _trace, _freshOutput, _freshAdvance, _distinct,
              _programmingOrder, _programmed, _replayDefinition,
              _pendingQuery, returned, _initialHistory, _replayHistory,
              _prefixSteps, _replaySteps, _replayFuelBound, _resources,
              _withinBudget⟩
          exact returned }
  | .noPair output operational =>
      { entryOracle := noPairBothProgrammed root.source.toSameTapeSource
          root.execution child.generated child.configuration
        entryProgram :=
          root.source.toSameTapeSource.origin.capability.start
            root.source.toSameTapeSource.observation
        programProvenance := SameTapeProgramProvenance.start
          (source := root.source)
        controller := recordedPrefixController
          (noPairBothProgrammed root.source.toSameTapeSource root.execution
            child.generated child.configuration).history.length
          (freezeAdversaryQ1
            (noPairPost root.source.toSameTapeSource))
        limits := noPairReplayLimits (noPairPost root.source.toSameTapeSource)
          output.pairs.length
        fuel := output.pairs.length
        run := output.replay
        returnedValue := output.returned
        exactRun := by
          rcases operational with ⟨exactReplay, _withinBudget⟩
          rcases exactReplay with
            ⟨_tape, _identity, _q1, _noPair, _firstReturned,
              _outputMissing, _advanceMissing, replayDefinition,
              _replayReturned, _trace, _records, _table, _programmed,
              _total, _fresh, _steps, _sameTape, _forgery, _resources⟩
          simpa [noPairReplay, Tag73SameTapeSource.toSameTapeSource] using
            replayDefinition
        normallyReturned := by
          rcases operational with ⟨exactReplay, _withinBudget⟩
          rcases exactReplay with
            ⟨_tape, _identity, _q1, _noPair, _firstReturned,
              _outputMissing, _advanceMissing, _replayDefinition,
              replayReturned, _trace, _records, _table, _programmed,
              _total, _fresh, _steps, _sameTape, _forgery, _resources⟩
          exact replayReturned }

@[simp] theorem child_continuation_run_is_actual_replay_run
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    (continuationOfRestrictedChild child).run = child.replayRun := by
  rcases child with ⟨generated, configuration, outcome, dispatched⟩
  cases outcome <;> rfl

@[simp] theorem child_continuation_returned_value_is_actual
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    (continuationOfRestrictedChild child).returnedValue =
      child.returnedValue := by
  rcases child with ⟨generated, configuration, outcome, dispatched⟩
  cases outcome <;> rfl

theorem child_continuation_has_exact_same_tape_program_provenance
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    SameTapeProgramProvenance root.source
      (continuationOfRestrictedChild child).entryProgram :=
  (continuationOfRestrictedChild child).programProvenance

theorem child_continuation_preserves_cumulative_programming
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    (continuationOfRestrictedChild child).run.oracle.programmingHistory =
      (continuationOfRestrictedChild child).entryOracle.programmingHistory := by
  let continuation := continuationOfRestrictedChild child
  rw [continuation.exactRun]
  exact run_machine_preserves_programming_history continuation.controller
    continuation.limits .extractorReplay continuation.fuel
      continuation.entryOracle continuation.entryProgram

theorem child_continuation_trace_is_replay_tagged
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (child : RestrictedReplayChild root) :
    ∀ record ∈ (continuationOfRestrictedChild child).proverTrace,
      record.actor = .extractorReplay := by
  let continuation := continuationOfRestrictedChild child
  rw [ResumeDerivedContinuation.proverTrace, continuation.exactRun]
  exact run_machine_history_since_has_actor continuation.controller
    continuation.limits .extractorReplay continuation.fuel
      continuation.entryOracle continuation.entryProgram

/-! ## Honest returned-child graph node -/

/-- An actual node consists only of one dispatcher child and a normal return
of the mixed-history verifier on that child's own parsed DAG.  Its source,
replay continuation, returned value, and concrete execution are all computed
from those operations. -/
structure ActualReturnedChildNode
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload) where
  child : RestrictedReplayChild root
  verifierController : AdaptiveController
  verifierLimits : OracleLimits
  verifierFuel : Nat
  verifierResult : VerifierPlanResult
  verifierReturned :
    (runFullVerifierPlanForProverHistory verifierController verifierLimits
      verifierFuel child.replayRun.oracle child.replayRun.oracle
        child.returnedDag.tape).halt = .returned verifierResult

def ActualReturnedChildNode.continuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root) :
    ResumeDerivedContinuation root.source :=
  continuationOfRestrictedChild node.child

/-- The immutable source of every returned child is definitionally the root
source.  In particular, the node has no field in which a different black box,
hidden tape, identity, or observation could be supplied. -/
def ActualReturnedChildNode.source
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (_node : ActualReturnedChildNode root) :
    Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement Proof
      Payload :=
  root.source

def ActualReturnedChildNode.verifier
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root) :
    ReturnedValueProverHistoryVerifier node.child.returnedValue :=
  returnedChildProverHistoryVerifier node.child node.verifierController
    node.verifierLimits node.verifierFuel node.verifierResult
      node.verifierReturned

def ActualReturnedChildNode.execution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root) :
    ReparsedDagExecution node.child.returnedValue :=
  node.verifier.reparsedExecution

@[simp] theorem child_node_retains_original_black_box_and_hidden_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root) :
    node.source.blackBox = root.source.blackBox ∧
      node.source.hiddenTape = root.source.hiddenTape ∧
      node.source.tapeIdentity = root.source.tapeIdentity ∧
      node.source.observation = root.source.observation := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem child_node_replay_and_return_are_actual_dispatch_outputs
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root) :
    node.continuation.run = node.child.replayRun ∧
      node.continuation.returnedValue = node.child.returnedValue ∧
      node.continuation.run.halt =
        .returned node.continuation.returnedValue := by
  exact ⟨child_continuation_run_is_actual_replay_run node.child,
    child_continuation_returned_value_is_actual node.child,
    node.continuation.normallyReturned⟩

theorem child_node_execution_uses_returned_dag_and_final_verifier_table
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root) :
    node.execution.execution.tape = node.child.returnedDag.tape ∧
      node.execution.table = node.verifier.finalTable ∧
      node.execution.execution.trace.actionReplies =
        node.verifierResult.actionReplies := by
  exact ⟨first_execution_retains_same_tape node.execution.execution,
    returned_value_reparsed_execution_uses_final_table node.verifier,
    returned_value_reparsed_execution_has_exact_replies node.verifier⟩

theorem child_node_every_generated_prefix_is_complete_seen_nonempty_bound
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag) :
    let restoration := concreteRestoration node.execution.execution generated
    IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot
        node.execution.execution.interactiveState ∧
      NonemptyVerifierHistory node.execution.execution.interactiveState ∧
      restoration.snapshot.bindings =
        FixedBindings.ofContext node.child.returnedDag.tape.messages.context ∧
      restoration.oracleTable = node.verifier.finalTable := by
  exact returned_child_execution_every_generated_prefix_is_legal node.child
    node.verifierController node.verifierLimits node.verifierFuel
      node.verifierResult node.verifierReturned generated

/-! ## Why the depth-one dispatcher cannot be reused recursively -/

/-- Calling the existing dispatcher on a child execution still classifies
against the original root adversary Q1.  It does not inspect the actual
resume-derived continuation trace. -/
noncomputable def legacyDispatchAtChild
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration) :=
  dispatchGeneratedReplayBranch root.source.toSameTapeSource
    node.execution.execution generated configuration

theorem legacy_child_dispatch_success_uses_original_adversary_q1
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration)
    (outcome : ReplayBranchOutcome root.source.toSameTapeSource
      node.execution.execution generated configuration)
    (_success : legacyDispatchAtChild node generated configuration =
      .ok outcome) :
    match outcome with
    | .atomic output _ =>
        firstGeneratedPairOccurrenceInFrozenQ1
          root.source.origin.firstRun.stateAtAdversaryHalt
          node.execution.execution generated = some output.occurrence
    | .noPair _ _ =>
        firstGeneratedPairOccurrenceInFrozenQ1
          root.source.origin.firstRun.stateAtAdversaryHalt
          node.execution.execution generated = none := by
  cases outcome with
  | atomic output operational =>
      rcases operational with
        ⟨_tape, _identity, _q1, occurrence, _rest⟩
      simpa [Tag73SameTapeSource.origin] using occurrence
  | noPair output operational =>
      simpa [Tag73SameTapeSource.origin] using operational.1.2.2.2.1

theorem child_continuation_records_are_not_original_adversary_q1_records
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root) :
    ∀ record ∈ node.continuation.proverTrace,
      record ∉ freezeAdversaryQ1
        root.source.origin.firstRun.stateAtAdversaryHalt := by
  intro record replayMember frozenMember
  have replayActor : record.actor = .extractorReplay :=
    child_continuation_trace_is_replay_tagged node.child record replayMember
  have adversaryActor : record.actor = .adversary :=
    frozen_q1_contains_only_adversary_calls
      root.source.origin.firstRun.stateAtAdversaryHalt record frozenMember
  rw [replayActor] at adversaryActor
  exact extractor_replay_actor_ne_adversary adversaryActor

/-! ## Exact node-local pause -/

/-- Search the actual node-local continuation trace, with no actor relabelling,
for the first occurrence of either half of a generated child squeeze. -/
noncomputable def firstGeneratedPairOccurrenceInContinuation
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag) :
    Option PairOccurrenceSplit :=
  firstEitherInputOccurrence
    (generatedPairInput node.execution.execution generated .output)
    (generatedPairInput node.execution.execution generated .advance)
    node.continuation.proverTrace

/-- The exact segment-local lemma for a recursive present-pair edge.  It asks
for no arbitrary checkpoint: the pause must be produced by running the
node's provenanced entry program from its exact cumulative entry oracle while
replaying the actual prefix records.  The next residual query must be the
chosen generated-pair input.

This proposition is intentionally not a field of `ActualReturnedChildNode`;
the next theorem derives it from the actual normally returned run. -/
def ContinuationPairPauseProperty
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag) : Prop :=
  ∀ occurrence,
    firstGeneratedPairOccurrenceInContinuation node generated =
        some occurrence →
    let prefixRun := runPrefix
      (recordedPrefixController node.continuation.entryOracle.history.length
        occurrence.before)
      node.continuation.limits .extractorReplay occurrence.before.length
      node.continuation.entryOracle node.continuation.entryProgram
    ∃ residual pendingInput pendingContinuation,
      prefixRun.halt = .paused residual ∧
      residual = .query pendingInput pendingContinuation ∧
      pendingInput = occurrence.chosen.input ∧
      queryAnswerTrace
        (historySince node.continuation.entryOracle prefixRun.oracle) =
          queryAnswerTrace occurrence.before

/-- The node-local pause property follows from the actual normally returned
run.  It is not an interface premise: the residual query is recovered by
replaying the exact chronological prefix of that run. -/
theorem continuation_pair_pause_property
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag) :
    ContinuationPairPauseProperty node generated := by
  intro occurrence found
  let continuation := node.continuation
  have foundInRun : firstEitherInputOccurrence
      (generatedPairInput node.execution.execution generated .output)
      (generatedPairInput node.execution.execution generated .advance)
      (historySince continuation.entryOracle continuation.run.oracle) =
        some occurrence := by
    simpa [firstGeneratedPairOccurrenceInContinuation,
      ResumeDerivedContinuation.proverTrace, continuation] using found
  have decomposition := (first_either_input_occurrence_spec
    (generatedPairInput node.execution.execution generated .output)
    (generatedPairInput node.execution.execution generated .advance)
    (historySince continuation.entryOracle continuation.run.oracle)
    occurrence foundInRun).1
  have returnedRun :
      (runMachine continuation.controller continuation.limits
        .extractorReplay continuation.fuel continuation.entryOracle
          continuation.entryProgram).halt =
        .returned continuation.returnedValue := by
    rw [← continuation.exactRun]
    exact continuation.normallyReturned
  have decompositionRun :
      historySince continuation.entryOracle
          (runMachine continuation.controller continuation.limits
            .extractorReplay continuation.fuel continuation.entryOracle
              continuation.entryProgram).oracle =
        occurrence.before ++ occurrence.chosen :: occurrence.after := by
    rw [← continuation.exactRun]
    exact decomposition
  simpa [continuation] using
    returned_run_first_occurrence_replays_to_exact_pause
      continuation.controller continuation.limits .extractorReplay
      continuation.fuel continuation.entryOracle continuation.entryProgram
      continuation.returnedValue occurrence returnedRun decompositionRun

/-! ## Continuation-local present-pair replay -/

structure ContinuationAtomicPairReplayOutput
    (Statement Proof Payload : Type*) where
  occurrence : PairOccurrenceSplit
  chosenHalf : SqueezeHalf
  prefixRun : PrefixRun
    (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  residualProgram : OracleMachine
    (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  pendingInput : ShaInput
  pendingContinuation : ShaOutput → OracleMachine
    (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  assignedPendingOutput : ShaOutput
  programming : PairProgrammingResult
  replayRun : MachineRun
    (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  returned : CheckedTag73AdversaryReturnedValue Statement Proof Payload
  resources : ResourceUse

/-- Purely operational legality for a present-pair child edge.  The entry
program's same-tape provenance is carried by `node.continuation`; this
predicate adds only equations computed at this edge. -/
def IsOperationalContinuationAtomicPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration)
    (output : ContinuationAtomicPairReplayOutput Statement Proof Payload) : Prop :=
  firstGeneratedPairOccurrenceInContinuation node generated =
      some output.occurrence ∧
  output.prefixRun = runPrefix
    (recordedPrefixController node.continuation.entryOracle.history.length
      output.occurrence.before)
    node.continuation.limits .extractorReplay output.occurrence.before.length
    node.continuation.entryOracle node.continuation.entryProgram ∧
  output.prefixRun.halt = .paused output.residualProgram ∧
  output.residualProgram =
    .query output.pendingInput output.pendingContinuation ∧
  output.pendingInput = output.occurrence.chosen.input ∧
  halfForPairInput node.execution.execution generated output.pendingInput =
    some output.chosenHalf ∧
  output.assignedPendingOutput =
    assignedPairOutput configuration output.chosenHalf ∧
  programAtomicPair node.execution.execution generated configuration
      output.prefixRun.oracle = .ok output.programming ∧
  output.replayRun = runMachine configuration.postForkController
    configuration.oracleLimits .extractorReplay configuration.replayFuel
    output.programming.afterBoth
    (.query output.pendingInput output.pendingContinuation) ∧
  (∃ afterPendingQuery : OracleState,
    queryOracle configuration.postForkController configuration.oracleLimits
      .extractorReplay output.programming.afterBoth output.pendingInput =
        .ok (output.assignedPendingOutput, afterPendingQuery)) ∧
  output.replayRun.halt = .returned output.returned ∧
  output.resources = atomicPairResourceUse configuration.firstRunUse
    output.prefixRun.steps output.replayRun.steps output.replayRun.oracle ∧
  WithinBudget output.resources configuration.budget

/-- Execute one continuation-local present-pair fork.  Every checkpoint and
residual is obtained by evaluating `runPrefix`; failures are classified by
the existing atomic replay failure type. -/
noncomputable def constructContinuationAtomicPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration) :
    Except AtomicPairReplayFailure
      {output : ContinuationAtomicPairReplayOutput Statement Proof Payload //
        IsOperationalContinuationAtomicPairReplay node generated configuration
          output} := by
  classical
  exact match occurrenceFound : firstGeneratedPairOccurrenceInContinuation
      node generated with
  | none => .error .missingPairOccurrence
  | some occurrence =>
      let prefixRun := runPrefix
        (recordedPrefixController node.continuation.entryOracle.history.length
          occurrence.before)
        node.continuation.limits .extractorReplay occurrence.before.length
        node.continuation.entryOracle node.continuation.entryProgram
      match prefixHalt : prefixRun.halt with
      | .returned _ | .oracleAbort _ => .error .replayEndedBeforePair
      | .paused residual =>
          match residualShape : residual with
          | .pure _ | .abort _ => .error .replayEndedBeforePair
          | .query pendingInput next =>
              if pendingMismatch : pendingInput ≠ occurrence.chosen.input then
                .error .replayDidNotReachChosenInput
              else
                have pendingChosen : pendingInput = occurrence.chosen.input :=
                  Classical.byContradiction fun unequal =>
                    pendingMismatch unequal
                match halfClassification : halfForPairInput
                    node.execution.execution generated pendingInput with
                | none => .error .replayDidNotReachChosenInput
                | some chosenHalf =>
                    match programmingSuccess : programAtomicPair
                        node.execution.execution generated configuration
                        prefixRun.oracle with
                    | .error reason => .error reason
                    | .ok programming =>
                        if configuration.replayFuel = 0 then .error .timeout
                        else
                          let replayRun := runMachine
                            configuration.postForkController
                            configuration.oracleLimits .extractorReplay
                            configuration.replayFuel programming.afterBoth
                            (.query pendingInput next)
                          match replayHalt : replayRun.halt with
                          | .outOfFuel => .error .timeout
                          | .oracleAbort reason => .error (.replayAbort reason)
                          | .returned result =>
                              let resources := atomicPairResourceUse
                                configuration.firstRunUse prefixRun.steps
                                replayRun.steps replayRun.oracle
                              if within : WithinBudget resources
                                  configuration.budget then
                                let output :
                                    ContinuationAtomicPairReplayOutput
                                      Statement Proof Payload :=
                                  { occurrence := occurrence
                                    chosenHalf := chosenHalf
                                    prefixRun := prefixRun
                                    residualProgram := residual
                                    pendingInput := pendingInput
                                    pendingContinuation := next
                                    assignedPendingOutput :=
                                      assignedPairOutput configuration chosenHalf
                                    programming := programming
                                    replayRun := replayRun
                                    returned := result
                                    resources := resources }
                                have pendingHalf :=
                                  half_for_pair_input_some_is_exact
                                    node.execution.execution generated
                                    pendingInput chosenHalf halfClassification
                                have pendingProgrammed :
                                    (lookupEntry programming.afterBoth
                                      pendingInput).map
                                        AspisK1.V7FsAokExperiment.TableEntry.output =
                                      some (assignedPairOutput configuration
                                        chosenHalf) := by
                                  rw [pendingHalf]
                                  exact (program_atomic_pair_success_exact
                                    node.execution.execution generated
                                    configuration prefixRun.oracle programming
                                    programmingSuccess).2.2.2.2 chosenHalf
                                have pendingQuery : ∃ nextState,
                                    queryOracle
                                      configuration.postForkController
                                      configuration.oracleLimits
                                      .extractorReplay programming.afterBoth
                                      pendingInput =
                                        .ok (assignedPairOutput configuration
                                          chosenHalf, nextState) := by
                                  obtain ⟨actual, nextState, queried⟩ :=
                                    run_machine_returned_query_exposes_first_call
                                      configuration.postForkController
                                      configuration.oracleLimits
                                      .extractorReplay configuration.replayFuel
                                      programming.afterBoth pendingInput next
                                      result replayHalt
                                  have actualAssigned :=
                                    query_oracle_success_uses_cached_lookup_answer
                                      configuration.postForkController
                                      configuration.oracleLimits
                                      .extractorReplay programming.afterBoth
                                      nextState pendingInput actual
                                      (assignedPairOutput configuration chosenHalf)
                                      pendingProgrammed queried
                                  rw [actualAssigned] at queried
                                  exact ⟨nextState, queried⟩
                                .ok ⟨output, occurrenceFound, rfl,
                                  (by simpa [output, residualShape] using
                                    prefixHalt),
                                  residualShape, pendingChosen,
                                  halfClassification, rfl,
                                  programmingSuccess, rfl, pendingQuery,
                                  replayHalt, rfl, within⟩
                              else .error .resourceBudget

/-! ## Continuation-local no-pair replay

When neither squeeze input occurs in the node-local continuation, recursion
does not create a new start capability.  It reuses the same provenanced entry
program, but starts it from the continuation's final table after adding the
two fresh pair answers.  Thus every answer on the already returned path is
cached and the same parsed proof is returned. -/

noncomputable def continuationNoPairPost
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : Tag73SameTapeSource HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (continuation : ResumeDerivedContinuation source) : OracleState :=
  continuation.run.oracle

noncomputable def continuationNoPairFirstProgrammed
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration) : OracleState :=
  appendProgrammedPoint .extractorReplay
    (continuationNoPairPost node.continuation)
    { input := generatedPairInput node.execution.execution generated .output
      output := configuration.forkOutput }

noncomputable def continuationNoPairBothProgrammed
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration) : OracleState :=
  appendProgrammedPoint .extractorReplay
    (continuationNoPairFirstProgrammed node generated configuration)
    { input := generatedPairInput node.execution.execution generated .advance
      output := configuration.forkAdvance }

def continuationNoPairLimits (post : OracleState) (pathLength : Nat) :
    OracleLimits :=
  noPairReplayLimits post pathLength

noncomputable def continuationNoPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration)
    (pairs : List (ShaInput × ShaOutput)) :
    MachineRun (CheckedTag73AdversaryReturnedValue Statement Proof Payload) :=
  let post := continuationNoPairPost node.continuation
  let both := continuationNoPairBothProgrammed node generated configuration
  let limits := continuationNoPairLimits post pairs.length
  runMachine
    (recordedPrefixController both.history.length node.continuation.proverTrace)
    limits .extractorReplay pairs.length both node.continuation.entryProgram

structure ContinuationNoPairReplayOutput
    (Statement Proof Payload : Type*) where
  pairs : List (ShaInput × ShaOutput)
  replay : MachineRun
    (CheckedTag73AdversaryReturnedValue Statement Proof Payload)
  resources : ResourceUse

def continuationNoPairResourceUse (firstRunUse : ResourceUse)
    {Result : Type*} (replay : MachineRun Result) : ResourceUse :=
  couplingResourceUse firstRunUse 0 replay.steps replay.oracle

def IsExactContinuationNoPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration)
    (output : ContinuationNoPairReplayOutput Statement Proof Payload) : Prop :=
  firstGeneratedPairOccurrenceInContinuation node generated = none ∧
  lookupEntry (continuationNoPairPost node.continuation)
      (generatedPairInput node.execution.execution generated .output) = none ∧
  lookupEntry (continuationNoPairPost node.continuation)
      (generatedPairInput node.execution.execution generated .advance) = none ∧
  output.replay = continuationNoPairReplay node generated configuration
      output.pairs ∧
  output.replay.halt = .returned node.continuation.returnedValue ∧
  queryAnswerTrace
      (historySince
        (continuationNoPairBothProgrammed node generated configuration)
        output.replay.oracle) = output.pairs ∧
  (∀ record ∈ historySince
      (continuationNoPairBothProgrammed node generated configuration)
      output.replay.oracle,
    record.actor = .extractorReplay ∧
      record.input ≠
        generatedPairInput node.execution.execution generated .output ∧
      record.input ≠
        generatedPairInput node.execution.execution generated .advance) ∧
  output.replay.oracle.table =
      (continuationNoPairBothProgrammed node generated configuration).table ∧
  output.replay.oracle.programmingHistory.length =
      (continuationNoPairPost node.continuation).programmingHistory.length + 2 ∧
  output.replay.oracle.totalCalls =
      (continuationNoPairPost node.continuation).totalCalls +
        output.pairs.length ∧
  output.replay.oracle.freshCalls =
      (continuationNoPairPost node.continuation).freshCalls ∧
  output.replay.steps = output.pairs.length ∧
  output.resources = continuationNoPairResourceUse
    configuration.firstRunUse output.replay

def IsOperationalContinuationNoPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration)
    (output : ContinuationNoPairReplayOutput Statement Proof Payload) : Prop :=
  IsExactContinuationNoPairReplay node generated configuration output ∧
    WithinBudget output.resources configuration.budget

/-- Exact no-pair replay below a returned child.  The only hypotheses are the
results of concrete scans/lookups; the recursive dispatcher below obtains
them by case analysis. -/
theorem exact_continuation_no_pair_replay_exists
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {root : RestrictedReplayRoot HiddenTape TapeIdentity Observation Statement
      Proof Payload}
    (node : ActualReturnedChildNode root)
    (generated : GeneratedReplayPrefix node.child.returnedDag)
    (configuration : AtomicPairReplayConfiguration)
    (noPair : firstGeneratedPairOccurrenceInContinuation node generated = none)
    (outputMissing : lookupEntry (continuationNoPairPost node.continuation)
      (generatedPairInput node.execution.execution generated .output) = none)
    (advanceMissing : lookupEntry (continuationNoPairPost node.continuation)
      (generatedPairInput node.execution.execution generated .advance) = none) :
    ∃ output : ContinuationNoPairReplayOutput Statement Proof Payload,
      IsExactContinuationNoPairReplay node generated configuration output := by
  let continuation := node.continuation
  have returnedRun :
      (runMachine continuation.controller continuation.limits
        .extractorReplay continuation.fuel continuation.entryOracle
          continuation.entryProgram).halt =
        .returned continuation.returnedValue := by
    rw [← continuation.exactRun]
    exact continuation.normallyReturned
  obtain ⟨pairs, path, firstTrace, firstActors, finalAnswers⟩ :=
    run_machine_returned_has_exact_query_path continuation.controller
      continuation.limits .extractorReplay continuation.fuel
      continuation.entryOracle continuation.entryProgram
      continuation.returnedValue returnedRun
  have exactRunEq := continuation.exactRun
  rw [← exactRunEq] at firstTrace firstActors finalAnswers
  let post := continuationNoPairPost continuation
  let outputProgramming : Programming :=
    { input := generatedPairInput node.execution.execution generated .output
      output := configuration.forkOutput }
  let advanceProgramming : Programming :=
    { input := generatedPairInput node.execution.execution generated .advance
      output := configuration.forkAdvance }
  let firstProgrammed := continuationNoPairFirstProgrammed node generated
    configuration
  let bothProgrammed := continuationNoPairBothProgrammed node generated
    configuration
  let limits := continuationNoPairLimits post pairs.length
  have firstBudget : post.programmingHistory.length <
      limits.programmedPoints := by
    simp [limits, continuationNoPairLimits, noPairReplayLimits]
  have firstProgramming :
      programOracle limits .extractorReplay post outputProgramming =
        .ok firstProgrammed := by
    apply program_oracle_fresh_point_exact limits .extractorReplay post
      outputProgramming firstBudget
    simpa [post, continuationNoPairPost, outputProgramming] using outputMissing
  have distinct := generated_pair_inputs_are_distinct
    node.execution.execution generated
  have advanceAfterFirstMissing :
      lookupEntry firstProgrammed advanceProgramming.input = none := by
    apply append_programmed_point_other_input_remains_missing .extractorReplay
      post outputProgramming advanceProgramming.input
    · simpa [post, continuationNoPairPost, advanceProgramming] using
        advanceMissing
    · simpa [outputProgramming, advanceProgramming] using distinct
  have secondBudget : firstProgrammed.programmingHistory.length <
      limits.programmedPoints := by
    simp [firstProgrammed, continuationNoPairFirstProgrammed,
      appendProgrammedPoint, limits, continuationNoPairLimits,
      noPairReplayLimits, post, continuation]
  have secondProgramming :
      programOracle limits .extractorReplay firstProgrammed
        advanceProgramming = .ok bothProgrammed := by
    apply program_oracle_fresh_point_exact limits .extractorReplay
      firstProgrammed advanceProgramming secondBudget
        advanceAfterFirstMissing
  have answersPost : PreloadedPathAnswers post pairs := by
    intro pair member
    rw [← fixed_table_lookup_eq_lookup_entry_output]
    simpa [post, continuationNoPairPost] using finalAnswers pair member
  have answersFirst : PreloadedPathAnswers firstProgrammed pairs := by
    intro pair member
    exact append_programmed_point_preserves_answer .extractorReplay post
      outputProgramming pair.1 pair.2 (answersPost pair member)
  have answersBoth : PreloadedPathAnswers bothProgrammed pairs := by
    intro pair member
    exact append_programmed_point_preserves_answer .extractorReplay
      firstProgrammed advanceProgramming pair.1 pair.2
        (answersFirst pair member)
  let replayController := recordedPrefixController bothProgrammed.history.length
    continuation.proverTrace
  let replay := runMachine replayController limits .extractorReplay
    pairs.length bothProgrammed continuation.entryProgram
  have totalRoom : bothProgrammed.totalCalls + pairs.length ≤
      limits.totalCalls := by
    simp [bothProgrammed, continuationNoPairBothProgrammed,
      continuationNoPairFirstProgrammed,
      appendProgrammedPoint, limits, continuationNoPairLimits,
      noPairReplayLimits, post, continuation]
  obtain ⟨replayHalt, replayTrace, replayActors, replayTable,
      replayProgramming, replayTotal, replayFresh, replaySteps⟩ :=
    run_machine_preloaded_replay_history_since_exact replayController limits
      .extractorReplay pairs.length bothProgrammed continuation.entryProgram
      pairs continuation.returnedValue path answersBoth totalRoom (le_refl _)
  have freshRecords := (first_either_input_occurrence_none_iff
    (generatedPairInput node.execution.execution generated .output)
    (generatedPairInput node.execution.execution generated .advance)
    continuation.proverTrace).mp noPair
  have pairAbsent : ∀ pair ∈ pairs,
      pair.1 ≠ generatedPairInput node.execution.execution generated .output ∧
      pair.1 ≠ generatedPairInput node.execution.execution generated .advance := by
    intro pair member
    have mappedMember : pair ∈ queryAnswerTrace continuation.proverTrace := by
      change pair ∈ queryAnswerTrace
        (historySince continuation.entryOracle continuation.run.oracle)
      rw [firstTrace]
      exact member
    obtain ⟨record, recordMember, recordPair⟩ := List.mem_map.mp mappedMember
    have fresh := freshRecords record recordMember
    have inputEq : record.input = pair.1 := congrArg Prod.fst recordPair
    exact ⟨fun equal => fresh.1 (inputEq.trans equal),
      fun equal => fresh.2 (inputEq.trans equal)⟩
  let resources := continuationNoPairResourceUse configuration.firstRunUse
    replay
  let output : ContinuationNoPairReplayOutput Statement Proof Payload :=
    { pairs := pairs, replay := replay, resources := resources }
  refine ⟨output, noPair, outputMissing, advanceMissing, rfl,
    replayHalt, replayTrace, ?_, replayTable, ?_, ?_, ?_, replaySteps, rfl⟩
  · intro record member
    have actorEq := replayActors record member
    have pairMember : (record.input, record.output) ∈ pairs := by
      rw [← replayTrace]
      exact List.mem_map.mpr ⟨record, member, rfl⟩
    exact ⟨actorEq, (pairAbsent _ pairMember).1,
      (pairAbsent _ pairMember).2⟩
  · have lengths := congrArg List.length replayProgramming
    simpa [output, replay, bothProgrammed, continuationNoPairBothProgrammed,
      firstProgrammed, continuationNoPairFirstProgrammed,
      appendProgrammedPoint, post, continuationNoPairPost] using lengths
  · simpa [output, replay, bothProgrammed, continuationNoPairBothProgrammed,
      firstProgrammed, continuationNoPairFirstProgrammed,
      appendProgrammedPoint, post, continuationNoPairPost] using replayTotal
  · simpa [output, replay, bothProgrammed, continuationNoPairBothProgrammed,
      firstProgrammed, continuationNoPairFirstProgrammed,
      appendProgrammedPoint, post, continuationNoPairPost] using replayFresh

/-! ## Future-free interactive verifier state

`CompleteSnapshot tape` is useful for proving facts about one fixed deployed
execution, but its type contains the entire future `DeployedFixedTape`.
Restoration across a changed challenge cannot use that type as the interactive
state: later C2 and q16 data may change.  The following state retains exactly
the live verifier data and no future proof. -/

structure OpenTag73Snapshot where
  bindings : FixedBindings
  phase : VerifierPhase
  core : RuntimeCore

structure OpenTag73Transition where
  before : OpenTag73Snapshot
  action : VerifierAction
  reply : VerifierReply
  inputs : List ByteString
  after : OpenTag73Snapshot

structure OpenTag73VerifierState where
  current : OpenTag73Snapshot
  seen : List OpenTag73Snapshot
  transitions : List OpenTag73Transition

def openSnapshotOfComplete {tape : DeployedFixedTape}
    (snapshot : CompleteSnapshot tape) : OpenTag73Snapshot where
  bindings := snapshot.bindings
  phase := snapshot.phase
  core := snapshot.core

def openTransitionOfRecord {tape : DeployedFixedTape}
    (transition : TransitionRecord tape) : OpenTag73Transition where
  before := openSnapshotOfComplete transition.before
  action := transition.action
  reply := transition.reply
  inputs := transition.inputs
  after := openSnapshotOfComplete transition.after

def openStateOfInteractive {tape : DeployedFixedTape}
    (state : InteractiveVerifierState tape) : OpenTag73VerifierState where
  current := openSnapshotOfComplete state.current
  seen := state.seen.map openSnapshotOfComplete
  transitions := state.transitions.map openTransitionOfRecord

def initialOpenTag73Snapshot (bindings : FixedBindings) :
    OpenTag73Snapshot where
  bindings := bindings
  phase := .dummyNonempty
  core := initialCore

def initialOpenTag73VerifierState (bindings : FixedBindings) :
    OpenTag73VerifierState where
  current := initialOpenTag73Snapshot bindings
  seen := [initialOpenTag73Snapshot bindings]
  transitions := []

def applyOpenTag73Snapshot (snapshot : OpenTag73Snapshot)
    (action : VerifierAction) (reply : VerifierReply) :
    Option OpenTag73Snapshot :=
  match applyActionWorkErased snapshot.core action reply with
  | none => none
  | some nextCore => some
      { bindings := snapshot.bindings
        phase := .after action
        core := nextCore }

def advanceOpenTag73VerifierState (state : OpenTag73VerifierState)
    (action : VerifierAction) (reply : VerifierReply) :
    Option OpenTag73VerifierState :=
  match applyOpenTag73Snapshot state.current action reply with
  | none => none
  | some next => some
      { current := next
        seen := state.seen ++ [next]
        transitions := state.transitions ++
          [{ before := state.current
             action := action
             reply := reply
             inputs := actionInputs state.current.bindings state.current.core
               action
             after := next }] }

def OpenPreviouslySeen (snapshot : OpenTag73Snapshot)
    (state : OpenTag73VerifierState) : Prop :=
  snapshot ∈ state.seen

def OpenNonemptyVerifierHistory (state : OpenTag73VerifierState) : Prop :=
  state.seen ≠ []

@[simp] theorem initial_open_history_is_nonempty (bindings : FixedBindings) :
    OpenNonemptyVerifierHistory (initialOpenTag73VerifierState bindings) := by
  simp [OpenNonemptyVerifierHistory, initialOpenTag73VerifierState]

@[simp] theorem initial_open_snapshot_is_seen (bindings : FixedBindings) :
    OpenPreviouslySeen (initialOpenTag73Snapshot bindings)
      (initialOpenTag73VerifierState bindings) := by
  simp [OpenPreviouslySeen, initialOpenTag73VerifierState]

theorem apply_open_snapshot_preserves_fixed_bindings
    (snapshot next : OpenTag73Snapshot) (action : VerifierAction)
    (reply : VerifierReply)
    (applied : applyOpenTag73Snapshot snapshot action reply = some next) :
    next.bindings = snapshot.bindings := by
  unfold applyOpenTag73Snapshot at applied
  split at applied <;> try contradiction
  next nextCore _ =>
    simp only [Option.some.injEq] at applied
    subst next
    rfl

theorem open_squeeze_is_one_atomic_complete_transition
    (snapshot : OpenTag73Snapshot) (owner : SqueezeOwner) (block : Nat)
    (output advance : Digest256) :
    ∃ next : OpenTag73Snapshot,
      applyOpenTag73Snapshot snapshot (.squeezePair owner block)
          (.squeeze output advance) = some next ∧
      next.bindings = snapshot.bindings ∧
      next.phase = .after (.squeezePair owner block) ∧
      next.core.digest = advance ∧
      actionInputs snapshot.bindings snapshot.core
          (.squeezePair owner block) =
        [bytes snapshot.core.digest ++ [domSqueeze],
         bytes snapshot.core.digest ++ [domAdvance]] ∧
      bytes snapshot.core.digest ++ [domSqueeze] ≠
        bytes snapshot.core.digest ++ [domAdvance] := by
  let next : OpenTag73Snapshot :=
    { bindings := snapshot.bindings
      phase := .after (.squeezePair owner block)
      core := { snapshot.core with digest := advance } }
  refine ⟨next, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact squeeze_output_and_advance_inputs_are_distinct snapshot.core.digest

/-- C2 is supplied as the next prover action at the exact newly decoded
lambda/chi indices.  The open state has no field capable of freezing a future
C2 commitment from the original tape. -/
theorem open_state_allows_challenge_dependent_c2_after_rewind
    (snapshot : OpenTag73Snapshot) (salt : Digest256)
    (hasSalt : snapshot.core.c2Salt = some salt)
    (lambda₁ chi₁ lambda₂ chi₂ : Qm31Bytes)
    (commitment₁ : C2Commitment lambda₁ chi₁)
    (commitment₂ : C2Commitment lambda₂ chi₂)
    (output₁ output₂ : Digest256) :
    ∃ next₁ next₂ : OpenTag73Snapshot,
      applyOpenTag73Snapshot snapshot
          (.absorbC2 lambda₁ chi₁ commitment₁) (.single output₁) =
        some next₁ ∧
      applyOpenTag73Snapshot snapshot
          (.absorbC2 lambda₂ chi₂ commitment₂) (.single output₂) =
        some next₂ ∧
      next₁.bindings = snapshot.bindings ∧
      next₂.bindings = snapshot.bindings := by
  refine ⟨
    { bindings := snapshot.bindings
      phase := .after (.absorbC2 lambda₁ chi₁ commitment₁)
      core := { snapshot.core with digest := output₁ } },
    { bindings := snapshot.bindings
      phase := .after (.absorbC2 lambda₂ chi₂ commitment₂)
      core := { snapshot.core with digest := output₂ } }, ?_⟩
  simp [applyOpenTag73Snapshot, applyActionWorkErased, hasSalt]

theorem projected_snapshot_retains_only_live_fields
    {tape : DeployedFixedTape} (snapshot : CompleteSnapshot tape) :
    (openSnapshotOfComplete snapshot).bindings = snapshot.bindings ∧
      (openSnapshotOfComplete snapshot).phase = snapshot.phase ∧
      (openSnapshotOfComplete snapshot).core = snapshot.core := by
  exact ⟨rfl, rfl, rfl⟩

theorem projected_previously_seen_snapshot_is_open_seen
    {tape : DeployedFixedTape} (snapshot : CompleteSnapshot tape)
    (state : InteractiveVerifierState tape)
    (seen : PreviouslySeen snapshot state) :
    OpenPreviouslySeen (openSnapshotOfComplete snapshot)
      (openStateOfInteractive state) := by
  exact List.mem_map.mpr ⟨snapshot, seen, rfl⟩

theorem projected_nonempty_history_is_open_nonempty
    {tape : DeployedFixedTape} (state : InteractiveVerifierState tape)
    (nonempty : NonemptyVerifierHistory state) :
    OpenNonemptyVerifierHistory (openStateOfInteractive state) := by
  intro empty
  have originalEmpty : state.seen = [] := by
    cases values : state.seen with
    | nil => rfl
    | cons head tail =>
        simp [openStateOfInteractive, values] at empty
  exact nonempty originalEmpty

theorem concrete_restoration_projects_to_future_free_seen_state
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    let restoration := concreteRestoration execution generated
    OpenPreviouslySeen (openSnapshotOfComplete restoration.snapshot)
        (openStateOfInteractive execution.interactiveState) ∧
      OpenNonemptyVerifierHistory
        (openStateOfInteractive execution.interactiveState) ∧
      (openSnapshotOfComplete restoration.snapshot).bindings =
        FixedBindings.ofContext dag.tape.messages.context := by
  let restoration := concreteRestoration execution generated
  exact ⟨projected_previously_seen_snapshot_is_open_seen
      restoration.snapshot execution.interactiveState
      (restoration_snapshot_is_previously_seen restoration),
    projected_nonempty_history_is_open_nonempty execution.interactiveState
      (restoration_first_run_history_is_nonempty restoration),
    restoration_preserves_fixed_bindings restoration⟩

/-! ## Exact whole-tape-index obstruction -/

/-- The canonical dependent transport between old snapshots requires an
equality of their entire future tapes. -/
def IndexedSnapshotTransportWitness
    (parent child : DeployedFixedTape)
    (parentSnapshot : CompleteSnapshot parent)
    (childSnapshot : CompleteSnapshot child) : Prop :=
  ∃ sameTape : parent = child,
    sameTape ▸ parentSnapshot = childSnapshot

theorem indexed_snapshot_transport_implies_whole_future_tape_equality
    (parent child : DeployedFixedTape)
    (parentSnapshot : CompleteSnapshot parent)
    (childSnapshot : CompleteSnapshot child)
    (transport : IndexedSnapshotTransportWitness parent child parentSnapshot
      childSnapshot) :
    parent = child := by
  exact transport.choose

theorem unequal_future_tapes_have_no_indexed_snapshot_transport
    (parent child : DeployedFixedTape)
    (different : parent ≠ child)
    (parentSnapshot : CompleteSnapshot parent)
    (childSnapshot : CompleteSnapshot child) :
    ¬ IndexedSnapshotTransportWitness parent child parentSnapshot
      childSnapshot := by
  intro transport
  exact different
    (indexed_snapshot_transport_implies_whole_future_tape_equality parent child
      parentSnapshot childSnapshot transport)

/-! ## Same-tape return does not preserve an earlier whole-proof field -/

structure ToyWholeProof where
  earlierField : Digest256
  suffixField : Digest256

def overwriteEarlierFieldContinuation (answer : Digest256) :
    OracleMachine ToyWholeProof :=
  .pure { earlierField := answer, suffixField := answer }

def overwriteEarlierFieldBlackBox : SameTapeBlackBox PUnit PUnit
    ToyWholeProof where
  start _hiddenTape _observation :=
    .query [] overwriteEarlierFieldContinuation

@[simp] theorem same_hidden_tape_return_can_change_an_earlier_field
    (first second : Digest256) (different : first ≠ second) :
    let program := overwriteEarlierFieldBlackBox.start () ()
    program = .query [] overwriteEarlierFieldContinuation ∧
      (overwriteEarlierFieldContinuation first =
        .pure { earlierField := first, suffixField := first }) ∧
      (overwriteEarlierFieldContinuation second =
        .pure { earlierField := second, suffixField := second }) ∧
      ({ earlierField := first, suffixField := first } : ToyWholeProof) ≠
        { earlierField := second, suffixField := second } := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro equal
  exact different (congrArg ToyWholeProof.earlierField equal)

/-! The minimal next machine is therefore an open tail interpreter.  Its
input must be an operationally emitted post-checkpoint action/reply stream,
not a reparsed whole proof whose earlier fields are unconstrained. -/

def runOpenTag73Tail : OpenTag73VerifierState →
    List (VerifierAction × VerifierReply) → Option OpenTag73VerifierState
  | state, [] => some state
  | state, (action, reply) :: rest =>
      match advanceOpenTag73VerifierState state action reply with
      | none => none
      | some next => runOpenTag73Tail next rest

def OpenTailStartsAtRestoredSqueeze
    (snapshot : OpenTag73Snapshot) (owner : SqueezeOwner) (block : Nat)
    (forkOutput forkAdvance : Digest256)
    (tail : List (VerifierAction × VerifierReply)) : Prop :=
  ∃ rest,
    tail = ((.squeezePair owner block, .squeeze forkOutput forkAdvance) :: rest) ∧
      actionInputs snapshot.bindings snapshot.core
        (.squeezePair owner block) =
          [bytes snapshot.core.digest ++ [domSqueeze],
           bytes snapshot.core.digest ++ [domAdvance]]

/-! ## Why one continuation suffix is not the whole causal replay path -/

theorem suffix_only_scan_can_miss_an_ancestor_pair
    (outputInput advanceInput : ShaInput) (ancestor : QueryRecord)
    (hit : ancestor.input = outputInput ∨ ancestor.input = advanceInput) :
    firstEitherInputOccurrence outputInput advanceInput [] = none ∧
      firstEitherInputOccurrence outputInput advanceInput [ancestor] ≠ none := by
  constructor
  · rfl
  · simp [firstEitherInputOccurrence, hit]

/-- Minimal future-free interaction program.  Unlike `OracleMachine Result`,
this program exposes each next complete verifier action before receiving the
verifier reply.  A same-hidden-tape black box returning this type would give
the extractor an operational post-checkpoint tail; a whole-proof-only result
does not. -/
inductive OpenTag73TailProgram (Result : Type*) where
  | returned (result : Result)
  | rejected
  | step (action : VerifierAction)
      (next : VerifierReply → OpenTag73TailProgram Result)

structure OpenTag73TailBlackBox
    (HiddenTape Observation Result : Type*) where
  start : HiddenTape → Observation → OpenTag73TailProgram Result

/-! ## Schedule-constrained, future-free C1/lambda/chi/C2 machine

The live-state interpreter above deliberately says nothing about which action
is legal next.  This control layer covers the first adaptive protocol slice
without indexing its state by a future proof.  The fixed public prefix is
derived only from `FixedBindings`; C1 is submitted before its salt/absorb
steps; lambda and chi are decoded by bounded incremental sampling; and only
then can a commitment of type `C2Commitment lambda chi` be submitted.

`afterAdaptiveC2` is an explicit boundary, not terminal acceptance.  Extending
this control through the remaining sumcheck, work, OOD, q16, authentication,
and terminal phases requires an operational prover-message stream.  The
existing `SameTapeBlackBox` exposes only a final parsed proof, and the toy
countermodel above shows why that result cannot soundly be spliced in as such
a stream.  In particular, a child proof's stored challenge values, sampler
uses, circle points, and q16 search are not controller inputs: the future
whole-protocol controller must recompute them from its own paired replies. -/

def openFixedPrefixActions (bindings : FixedBindings) : List VerifierAction :=
  [.checkpoint .canonicalWire,
   .absorb .profile,
   .absorb .circleBasis,
   .absorb (.deployment bindings.context),
   .absorb (.statement bindings.statementDigest),
   .absorb (.hidingPrecommit bindings.context)]

theorem open_fixed_prefix_is_exact_deployed_prefix (messages : Messages) :
    openFixedPrefixActions (FixedBindings.ofContext messages.context) =
      eventsToActions (prefixBeforeC1 messages) := by
  simp [openFixedPrefixActions, prefixBeforeC1, eventsToActions, eventActions]
    <;> rfl

inductive OpenAdaptiveControl where
  | fixedPrefix (remaining : List VerifierAction)
  | awaitingC1
  | requestC1Salt (root : TypedMerkleRoot .initialC1)
  | absorbC1 (root : TypedMerkleRoot .initialC1)
  | sampleLambda (outputs : List Digest256)
  | sampleChi (lambda : Qm31Bytes) (outputs : List Digest256)
  | awaitingC2 (lambda chi : Qm31Bytes)
  | requestC2Salt (lambda chi : Qm31Bytes)
      (commitment : C2Commitment lambda chi)
  | absorbC2 (lambda chi : Qm31Bytes)
      (commitment : C2Commitment lambda chi)
  | afterAdaptiveC2 (lambda chi : Qm31Bytes)
  | rejected

def OpenAdaptiveControl.nextVerifierAction? :
    OpenAdaptiveControl → Option VerifierAction
  | .fixedPrefix [] => none
  | .fixedPrefix (action :: _) => some action
  | .awaitingC1 => none
  | .requestC1Salt _ => some (.requestRootSalt .initialC1)
  | .absorbC1 root => some (.absorbC1 root)
  | .sampleLambda outputs =>
      some (.squeezePair (.challenge .lambda) outputs.length)
  | .sampleChi _ outputs =>
      some (.squeezePair (.challenge .chi) outputs.length)
  | .awaitingC2 _ _ => none
  | .requestC2Salt _ _ _ => some (.requestRootSalt .foldedC2)
  | .absorbC2 lambda chi commitment =>
      some (.absorbC2 lambda chi commitment)
  | .afterAdaptiveC2 _ _ => none
  | .rejected => none

def finishFixedPrefixControl : List VerifierAction → OpenAdaptiveControl
  | [] => .awaitingC1
  | remaining => .fixedPrefix remaining

/-- Exact condition needed to identify a fixed-tape `blocksUsed` value with
the incremental controller's stopping point.  Existing full-trace decoder
agreement proves the second conjunct only; it does not currently prove this
strict-prefix failure condition. -/
def DecoderPrefixMinimal (decoders : DeterministicDecoders)
    (id : ChallengeId) (blocks : List Digest256) : Prop :=
  ∀ count, count < blocks.length →
    decoders.qm31Parameter id (blocks.take count) = none

def OpenAdaptiveControl.afterVerifierReply
    (decoders : DeterministicDecoders) :
    OpenAdaptiveControl → VerifierReply → Option OpenAdaptiveControl
  | .fixedPrefix [], _ => none
  | .fixedPrefix (_ :: remaining), _ =>
      some (finishFixedPrefixControl remaining)
  | .requestC1Salt root, .single _ => some (.absorbC1 root)
  | .absorbC1 _, .single _ => some (.sampleLambda [])
  | .sampleLambda outputs, .squeeze output _ =>
      let nextOutputs := outputs ++ [output]
      match decoders.qm31Parameter .lambda nextOutputs with
      | some lambda => some (.sampleChi lambda [])
      | none =>
          if nextOutputs.length < samplerBlockCap (.ordinaryQm31) then
            some (.sampleLambda nextOutputs)
          else
            some .rejected
  | .sampleChi lambda outputs, .squeeze output _ =>
      let nextOutputs := outputs ++ [output]
      match decoders.qm31Parameter .chi nextOutputs with
      | some chi => some (.awaitingC2 lambda chi)
      | none =>
          if nextOutputs.length < samplerBlockCap (.ordinaryQm31) then
            some (.sampleChi lambda nextOutputs)
          else
            some .rejected
  | .requestC2Salt lambda chi commitment, .single _ =>
      some (.absorbC2 lambda chi commitment)
  | .absorbC2 lambda chi _, .single _ =>
      some (.afterAdaptiveC2 lambda chi)
  | _, _ => none

inductive OpenControlledEvent where
  | proverC1 (root : TypedMerkleRoot .initialC1)
  | proverC2 (lambda chi : Qm31Bytes)
      (commitment : C2Commitment lambda chi)
  | verifier (action : VerifierAction) (reply : VerifierReply)

structure OpenControlledSnapshot where
  control : OpenAdaptiveControl
  live : OpenTag73Snapshot

structure OpenControlledTransition where
  before : OpenControlledSnapshot
  event : OpenControlledEvent
  after : OpenControlledSnapshot

structure OpenControlledVerifierState where
  current : OpenControlledSnapshot
  seen : List OpenControlledSnapshot
  transitions : List OpenControlledTransition

def initialOpenControlledVerifierState (bindings : FixedBindings) :
    OpenControlledVerifierState :=
  let current : OpenControlledSnapshot :=
    { control := .fixedPrefix (openFixedPrefixActions bindings)
      live := initialOpenTag73Snapshot bindings }
  { current := current, seen := [current], transitions := [] }

def appendOpenControlledSnapshot (state : OpenControlledVerifierState)
    (event : OpenControlledEvent) (next : OpenControlledSnapshot) :
    OpenControlledVerifierState :=
  { current := next
    seen := state.seen ++ [next]
    transitions := state.transitions ++
      [{ before := state.current, event := event, after := next }] }

def submitOpenC1 (state : OpenControlledVerifierState)
    (root : TypedMerkleRoot .initialC1)
    (_atC1 : state.current.control = .awaitingC1) :
    OpenControlledVerifierState :=
  let next : OpenControlledSnapshot :=
    { control := .requestC1Salt root, live := state.current.live }
  appendOpenControlledSnapshot state (.proverC1 root) next

def submitOpenC2 (state : OpenControlledVerifierState)
    (lambda chi : Qm31Bytes)
    (commitment : C2Commitment lambda chi)
    (_atC2 : state.current.control = .awaitingC2 lambda chi) :
    OpenControlledVerifierState :=
  let next : OpenControlledSnapshot :=
    { control := .requestC2Salt lambda chi commitment
      live := state.current.live }
  appendOpenControlledSnapshot state (.proverC2 lambda chi commitment) next

def advanceOpenControlledVerifier
    (decoders : DeterministicDecoders)
    (state : OpenControlledVerifierState) (reply : VerifierReply) :
    Option OpenControlledVerifierState := do
  let action ← state.current.control.nextVerifierAction?
  let nextLive ← applyOpenTag73Snapshot state.current.live action reply
  let nextControl ← state.current.control.afterVerifierReply decoders reply
  let next : OpenControlledSnapshot :=
    { control := nextControl, live := nextLive }
  pure (appendOpenControlledSnapshot state (.verifier action reply) next)

@[simp] theorem initial_open_controlled_history_is_nonempty
    (bindings : FixedBindings) :
    (initialOpenControlledVerifierState bindings).seen ≠ [] := by
  simp [initialOpenControlledVerifierState]

theorem submit_open_c1_preserves_live_state
    (state : OpenControlledVerifierState)
    (root : TypedMerkleRoot .initialC1)
    (atC1 : state.current.control = .awaitingC1) :
    (submitOpenC1 state root atC1).current.live = state.current.live := by
  rfl

theorem submit_open_c2_requires_the_decoded_indices
    (state : OpenControlledVerifierState)
    (lambda chi : Qm31Bytes)
    (commitment : C2Commitment lambda chi)
    (atC2 : state.current.control = .awaitingC2 lambda chi) :
    state.current.control = .awaitingC2 lambda chi ∧
      (submitOpenC2 state lambda chi commitment atC2).current.control =
        .requestC2Salt lambda chi commitment := by
  exact ⟨atC2, rfl⟩

theorem submit_open_c2_preserves_live_prefix
    (state : OpenControlledVerifierState)
    (lambda chi : Qm31Bytes)
    (commitment : C2Commitment lambda chi)
    (atC2 : state.current.control = .awaitingC2 lambda chi) :
    (submitOpenC2 state lambda chi commitment atC2).current.live =
      state.current.live := by
  rfl

theorem open_control_forces_lambda_then_chi_sampling
    (lambdaOutputs : List Digest256) (lambda : Qm31Bytes)
    (chiOutputs : List Digest256) :
    OpenAdaptiveControl.nextVerifierAction?
        (.sampleLambda lambdaOutputs) =
      some (.squeezePair (.challenge .lambda) lambdaOutputs.length) ∧
    OpenAdaptiveControl.nextVerifierAction?
        (.sampleChi lambda chiOutputs) =
      some (.squeezePair (.challenge .chi) chiOutputs.length) := by
  exact ⟨rfl, rfl⟩

theorem open_control_has_no_c2_action_while_sampling
    (lambdaOutputs : List Digest256) (lambda : Qm31Bytes)
    (chiOutputs : List Digest256) :
    (∀ action,
      OpenAdaptiveControl.nextVerifierAction?
          (.sampleLambda lambdaOutputs) = some action →
        ∃ block, action = .squeezePair (.challenge .lambda) block) ∧
    (∀ action,
      OpenAdaptiveControl.nextVerifierAction?
          (.sampleChi lambda chiOutputs) = some action →
        ∃ block, action = .squeezePair (.challenge .chi) block) := by
  constructor <;> intro action equal
  · exact ⟨lambdaOutputs.length, Option.some.inj equal.symm⟩
  · exact ⟨chiOutputs.length, Option.some.inj equal.symm⟩

theorem open_lambda_sampler_rejects_when_cap_is_exhausted
    (decoders : DeterministicDecoders) (outputs : List Digest256)
    (output advance : Digest256)
    (decodeFailed : decoders.qm31Parameter .lambda (outputs ++ [output]) = none)
    (capReached : samplerBlockCap (.ordinaryQm31) ≤
      (outputs ++ [output]).length) :
    OpenAdaptiveControl.afterVerifierReply decoders (.sampleLambda outputs)
        (.squeeze output advance) = some .rejected := by
  have cap : samplerBlockCap (.ordinaryQm31) ≤ outputs.length + 1 := by
    simpa using capReached
  simp [OpenAdaptiveControl.afterVerifierReply, decodeFailed,
    Nat.not_lt.mpr cap]

theorem open_chi_sampler_rejects_when_cap_is_exhausted
    (decoders : DeterministicDecoders) (lambda : Qm31Bytes)
    (outputs : List Digest256) (output advance : Digest256)
    (decodeFailed : decoders.qm31Parameter .chi (outputs ++ [output]) = none)
    (capReached : samplerBlockCap (.ordinaryQm31) ≤
      (outputs ++ [output]).length) :
    OpenAdaptiveControl.afterVerifierReply decoders
        (.sampleChi lambda outputs) (.squeeze output advance) =
      some .rejected := by
  have cap : samplerBlockCap (.ordinaryQm31) ≤ outputs.length + 1 := by
    simpa using capReached
  simp [OpenAdaptiveControl.afterVerifierReply, decodeFailed,
    Nat.not_lt.mpr cap]

theorem open_lambda_decode_success_forces_chi_next
    (decoders : DeterministicDecoders) (outputs : List Digest256)
    (output advance : Digest256) (lambda : Qm31Bytes)
    (decoded : decoders.qm31Parameter .lambda (outputs ++ [output]) =
      some lambda) :
    OpenAdaptiveControl.afterVerifierReply decoders (.sampleLambda outputs)
        (.squeeze output advance) = some (.sampleChi lambda []) := by
  simp [OpenAdaptiveControl.afterVerifierReply, decoded]

theorem open_chi_decode_success_is_the_only_c2_gate
    (decoders : DeterministicDecoders) (lambda : Qm31Bytes)
    (outputs : List Digest256) (output advance : Digest256)
    (chi : Qm31Bytes)
    (decoded : decoders.qm31Parameter .chi (outputs ++ [output]) =
      some chi) :
    OpenAdaptiveControl.afterVerifierReply decoders
        (.sampleChi lambda outputs) (.squeeze output advance) =
      some (.awaitingC2 lambda chi) := by
  simp [OpenAdaptiveControl.afterVerifierReply, decoded]

theorem advance_open_controlled_preserves_fixed_bindings
    (decoders : DeterministicDecoders)
    (state next : OpenControlledVerifierState) (reply : VerifierReply)
    (run : advanceOpenControlledVerifier decoders state reply = some next) :
    next.current.live.bindings = state.current.live.bindings := by
  rw [advanceOpenControlledVerifier] at run
  obtain ⟨action, actionEq, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextLive, liveEq, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨nextControl, controlEq, finalEq⟩ :=
    Option.bind_eq_some_iff.mp run
  have nextEq := Option.some.inj finalEq
  subst next
  exact apply_open_snapshot_preserves_fixed_bindings
    state.current.live nextLive action reply liveEq

theorem open_control_c2_can_change_after_a_challenge_fork
    (firstState secondState : OpenControlledVerifierState)
    (lambda₁ chi₁ lambda₂ chi₂ : Qm31Bytes)
    (commitment₁ : C2Commitment lambda₁ chi₁)
    (commitment₂ : C2Commitment lambda₂ chi₂)
    (sameRestoredPrefix : firstState.current.live = secondState.current.live)
    (atFirst : firstState.current.control = .awaitingC2 lambda₁ chi₁)
    (atSecond : secondState.current.control = .awaitingC2 lambda₂ chi₂) :
    (submitOpenC2 firstState lambda₁ chi₁ commitment₁ atFirst).current.control =
        .requestC2Salt lambda₁ chi₁ commitment₁ ∧
      (submitOpenC2 secondState lambda₂ chi₂ commitment₂ atSecond).current.control =
        .requestC2Salt lambda₂ chi₂ commitment₂ ∧
      (submitOpenC2 firstState lambda₁ chi₁ commitment₁ atFirst).current.live =
        (submitOpenC2 secondState lambda₂ chi₂ commitment₂ atSecond).current.live := by
  exact ⟨rfl, rfl, sameRestoredPrefix⟩

#print axioms child_continuation_run_is_actual_replay_run
#print axioms child_continuation_returned_value_is_actual
#print axioms child_continuation_has_exact_same_tape_program_provenance
#print axioms child_continuation_preserves_cumulative_programming
#print axioms child_continuation_trace_is_replay_tagged
#print axioms child_node_replay_and_return_are_actual_dispatch_outputs
#print axioms child_node_execution_uses_returned_dag_and_final_verifier_table
#print axioms child_node_every_generated_prefix_is_complete_seen_nonempty_bound
#print axioms legacy_child_dispatch_success_uses_original_adversary_q1
#print axioms child_continuation_records_are_not_original_adversary_q1_records
#print axioms continuation_pair_pause_property
#print axioms exact_continuation_no_pair_replay_exists
#print axioms initial_open_history_is_nonempty
#print axioms apply_open_snapshot_preserves_fixed_bindings
#print axioms open_squeeze_is_one_atomic_complete_transition
#print axioms open_state_allows_challenge_dependent_c2_after_rewind
#print axioms concrete_restoration_projects_to_future_free_seen_state
#print axioms indexed_snapshot_transport_implies_whole_future_tape_equality
#print axioms unequal_future_tapes_have_no_indexed_snapshot_transport
#print axioms same_hidden_tape_return_can_change_an_earlier_field
#print axioms suffix_only_scan_can_miss_an_ancestor_pair
#print axioms open_fixed_prefix_is_exact_deployed_prefix
#print axioms submit_open_c2_requires_the_decoded_indices
#print axioms open_control_has_no_c2_action_while_sampling
#print axioms open_lambda_sampler_rejects_when_cap_is_exhausted
#print axioms open_chi_sampler_rejects_when_cap_is_exhausted
#print axioms open_chi_decode_success_is_the_only_c2_gate
#print axioms advance_open_controlled_preserves_fixed_bindings
#print axioms open_control_c2_can_change_after_a_challenge_fork

end

end AspisK1.V7Tag73ResumeDerivedReplayNode
