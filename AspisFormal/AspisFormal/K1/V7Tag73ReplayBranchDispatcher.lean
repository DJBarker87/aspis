import AspisFormal.K1.V7Tag73AtomicPairReplay
import AspisFormal.K1.V7Tag73NoPairReplay

/-!
# Exhaustive generated-prefix replay dispatcher for Tag 73

For one generated squeeze checkpoint, the frozen adversary Q1 either contains
a first occurrence of one of the two atomic squeeze inputs or it does not.
This module computes that dichotomy once:

* the present branch invokes the concrete atomic-pair replay constructor;
* the absent branch checks the concrete first-run and initial-table conditions,
  then invokes the proved no-pair noninterference construction.

The no-pair theorem currently states existence of its exact cached replay in
`Prop`.  `constructNoPairReplay` packages that kernel-proved witness with
`Classical.choose`.  This makes the wrapper noncomputable, but it is not a
caller-supplied restore function, matcher, trace cover, or operational premise.
Every failure that precedes the choice is classified by executable case
analysis.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ReplayBranchDispatcher

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73ConcreteStateRestoration
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73NoPairReplay
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## Exact no-pair replay data -/

structure ConcreteNoPairReplayOutput
    (TapeIdentity Statement Proof Result : Type*) where
  tapeIdentity : TapeIdentity
  q1 : List QueryRecord
  returned : Result
  pairs : List (ShaInput × ShaOutput)
  replay : MachineRun Result
  resources : ResourceUse

def noPairPost
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result) : OracleState :=
  source.origin.firstRun.stateAtAdversaryHalt

noncomputable def noPairOutputProgramming
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration) : Programming where
  input := generatedPairInput execution generated .output
  output := configuration.forkOutput

noncomputable def noPairAdvanceProgramming
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration) : Programming where
  input := generatedPairInput execution generated .advance
  output := configuration.forkAdvance

noncomputable def noPairFirstProgrammed
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration) : OracleState :=
  appendProgrammedPoint .extractorReplay (noPairPost source)
    (noPairOutputProgramming execution generated configuration)

noncomputable def noPairBothProgrammed
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration) : OracleState :=
  appendProgrammedPoint .extractorReplay
    (noPairFirstProgrammed source execution generated configuration)
    (noPairAdvanceProgramming execution generated configuration)

noncomputable def noPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (pairs : List (ShaInput × ShaOutput)) : MachineRun Result :=
  let post := noPairPost source
  let both := noPairBothProgrammed source execution generated configuration
  let limits := noPairReplayLimits post pairs.length
  runMachine
    (recordedPrefixController both.history.length (freezeAdversaryQ1 post))
    limits .extractorReplay pairs.length both
    (source.origin.capability.start source.observation)

def noPairResourceUse (firstRunUse : ResourceUse)
    {Result : Type*} (replay : MachineRun Result) : ResourceUse :=
  couplingResourceUse firstRunUse 0 replay.steps replay.oracle

def IsExactNoPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output : ConcreteNoPairReplayOutput TapeIdentity Statement Proof Result) :
    Prop :=
  output.tapeIdentity = source.origin.capability.tapeIdentity ∧
  source.origin.capability.tapeIdentity = source.origin.firstRun.tapeIdentity ∧
  output.q1 = source.origin.firstRun.q1 ∧
  firstGeneratedPairOccurrenceInFrozenQ1
      source.origin.firstRun.stateAtAdversaryHalt execution generated = none ∧
  source.origin.firstExecution.halt = .returned output.returned ∧
  lookupEntry source.initialOracle
      (generatedPairInput execution generated .output) = none ∧
  lookupEntry source.initialOracle
      (generatedPairInput execution generated .advance) = none ∧
  output.replay = noPairReplay source execution generated configuration
    output.pairs ∧
  output.replay.halt = .returned output.returned ∧
  queryAnswerTrace
      (historySince
        (noPairBothProgrammed source execution generated configuration)
        output.replay.oracle) = output.pairs ∧
  (∀ record ∈ historySince
      (noPairBothProgrammed source execution generated configuration)
      output.replay.oracle,
    record.actor = .extractorReplay ∧
      record.input ≠ generatedPairInput execution generated .output ∧
      record.input ≠ generatedPairInput execution generated .advance) ∧
  output.replay.oracle.table =
      (noPairBothProgrammed source execution generated configuration).table ∧
  output.replay.oracle.programmingHistory.length =
      (noPairPost source).programmingHistory.length + 2 ∧
  output.replay.oracle.totalCalls =
      (noPairPost source).totalCalls + output.pairs.length ∧
  output.replay.oracle.freshCalls = (noPairPost source).freshCalls ∧
  output.replay.steps = output.pairs.length ∧
  source.origin.capability.start source.observation =
      source.blackBox.start source.hiddenTape source.observation ∧
  source.origin.firstRun.forgery = source.forgeryOf output.returned ∧
  output.resources = noPairResourceUse configuration.firstRunUse output.replay

def IsOperationalNoPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output : ConcreteNoPairReplayOutput TapeIdentity Statement Proof Result) :
    Prop :=
  IsExactNoPairReplay source execution generated configuration output ∧
  WithinBudget output.resources configuration.budget

theorem exact_no_pair_replay_exists
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (result : Result)
    (returned : source.origin.firstExecution.halt = .returned result)
    (outputInitialMissing : lookupEntry source.initialOracle
      (generatedPairInput execution generated .output) = none)
    (advanceInitialMissing : lookupEntry source.initialOracle
      (generatedPairInput execution generated .advance) = none)
    (noPair : firstGeneratedPairOccurrenceInFrozenQ1
      source.origin.firstRun.stateAtAdversaryHalt execution generated = none) :
    ∃ output : ConcreteNoPairReplayOutput TapeIdentity Statement Proof Result,
      IsExactNoPairReplay source execution generated configuration output := by
  obtain ⟨pairs, replayHalt, replayTrace, replayRecords, replayTable,
      programmed, total, fresh, steps, sameTape, forgery⟩ :=
    generated_squeeze_no_pair_replay source execution generated result returned
      configuration.forkOutput configuration.forkAdvance outputInitialMissing
      advanceInitialMissing noPair
  let replay := noPairReplay source execution generated configuration pairs
  let output : ConcreteNoPairReplayOutput TapeIdentity Statement Proof Result :=
    { tapeIdentity := source.origin.capability.tapeIdentity
      q1 := source.origin.firstRun.q1
      returned := result
      pairs := pairs
      replay := replay
      resources := noPairResourceUse configuration.firstRunUse replay }
  refine ⟨output, ?_⟩
  refine ⟨rfl, (source_origin_identity source).symm, rfl, noPair, returned,
    outputInitialMissing, advanceInitialMissing, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, sameTape, forgery, rfl⟩
  · simpa [output, replay, noPairReplay, noPairPost,
      noPairBothProgrammed, noPairFirstProgrammed, noPairOutputProgramming,
      noPairAdvanceProgramming] using replayHalt
  · simpa [output, replay, noPairReplay, noPairPost,
      noPairBothProgrammed, noPairFirstProgrammed, noPairOutputProgramming,
      noPairAdvanceProgramming] using replayTrace
  · simpa [output, replay, noPairReplay, noPairPost,
      noPairBothProgrammed, noPairFirstProgrammed, noPairOutputProgramming,
      noPairAdvanceProgramming] using replayRecords
  · simpa [output, replay, noPairReplay, noPairPost,
      noPairBothProgrammed, noPairFirstProgrammed, noPairOutputProgramming,
      noPairAdvanceProgramming] using replayTable
  · simpa [output, replay, noPairReplay, noPairPost,
      noPairBothProgrammed, noPairFirstProgrammed, noPairOutputProgramming,
      noPairAdvanceProgramming] using programmed
  · simpa [output, replay, noPairReplay, noPairPost,
      noPairBothProgrammed, noPairFirstProgrammed, noPairOutputProgramming,
      noPairAdvanceProgramming] using total
  · simpa [output, replay, noPairReplay, noPairPost,
      noPairBothProgrammed, noPairFirstProgrammed, noPairOutputProgramming,
      noPairAdvanceProgramming] using fresh
  · simpa [output, replay, noPairReplay, noPairPost,
      noPairBothProgrammed, noPairFirstProgrammed, noPairOutputProgramming,
      noPairAdvanceProgramming] using steps

/-! ## Exhaustive dispatcher -/

inductive ReplayBranchFailure where
  | atomic (reason : AtomicPairReplayFailure)
  | firstRunOracleAbort (reason : OracleAbort)
  | firstRunTimeout
  | initialInputConflict (half : SqueezeHalf)
  | noPairResourceBudget
  deriving DecidableEq, Repr

inductive ReplayBranchOutcome
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration) where
  | atomic
      (output : AtomicPairReplayOutput TapeIdentity Statement Proof Result)
      (operational : IsOperationalAtomicPairReplay source.origin execution
        generated configuration output)
  | noPair
      (output : ConcreteNoPairReplayOutput TapeIdentity Statement Proof Result)
      (operational : IsOperationalNoPairReplay source execution generated
        configuration output)

noncomputable def constructNoPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (result : Result)
    (returned : source.origin.firstExecution.halt = .returned result)
    (outputInitialMissing : lookupEntry source.initialOracle
      (generatedPairInput execution generated .output) = none)
    (advanceInitialMissing : lookupEntry source.initialOracle
      (generatedPairInput execution generated .advance) = none)
    (noPair : firstGeneratedPairOccurrenceInFrozenQ1
      source.origin.firstRun.stateAtAdversaryHalt execution generated = none) :
    Except ReplayBranchFailure
      {output : ConcreteNoPairReplayOutput TapeIdentity Statement Proof Result //
        IsOperationalNoPairReplay source execution generated configuration
          output} := by
  classical
  let witnessExists := exact_no_pair_replay_exists source execution generated
    configuration result returned outputInitialMissing advanceInitialMissing
      noPair
  let output := Classical.choose witnessExists
  have exactOutput := Classical.choose_spec witnessExists
  if within : WithinBudget output.resources configuration.budget then
    exact .ok ⟨output, exactOutput, within⟩
  else
    exact .error .noPairResourceBudget

noncomputable def dispatchGeneratedReplayBranch
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration) :
    Except ReplayBranchFailure
      (ReplayBranchOutcome source execution generated configuration) := by
  classical
  exact match occurrence : firstGeneratedPairOccurrenceInFrozenQ1
      source.origin.firstRun.stateAtAdversaryHalt execution generated with
  | some _ =>
      match constructAtomicPairReplay source execution generated configuration with
      | .error reason => .error (.atomic reason)
      | .ok output => .ok (.atomic output.1 output.2)
  | none =>
      match returned : source.origin.firstExecution.halt with
      | .oracleAbort reason => .error (.firstRunOracleAbort reason)
      | .outOfFuel => .error .firstRunTimeout
      | .returned result =>
          match outputFound : lookupEntry source.initialOracle
              (generatedPairInput execution generated .output) with
          | some _ => .error (.initialInputConflict .output)
          | none =>
              match advanceFound : lookupEntry source.initialOracle
                  (generatedPairInput execution generated .advance) with
              | some _ => .error (.initialInputConflict .advance)
              | none =>
                  match constructNoPairReplay source execution generated
                      configuration result returned outputFound advanceFound
                        occurrence with
                  | .error reason => .error reason
                  | .ok output => .ok (.noPair output.1 output.2)

/-! ## Classification, preservation and restoration -/

/-- The actual classifier is exhaustive by the `Option` returned from the
concrete first-occurrence scan. -/
theorem generated_pair_occurrence_is_some_or_none
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (state : OracleState) (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    (∃ occurrence, firstGeneratedPairOccurrenceInFrozenQ1 state execution
        generated = some occurrence) ∨
      firstGeneratedPairOccurrenceInFrozenQ1 state execution generated = none := by
  cases found : firstGeneratedPairOccurrenceInFrozenQ1 state execution generated with
  | none => exact Or.inr rfl
  | some occurrence => exact Or.inl ⟨occurrence, rfl⟩

theorem dispatch_success_classifies_branch
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (outcome : ReplayBranchOutcome source execution generated configuration)
    (success : dispatchGeneratedReplayBranch source execution generated
      configuration = .ok outcome) :
    match outcome with
    | .atomic output _ =>
        firstGeneratedPairOccurrenceInFrozenQ1
          source.origin.firstRun.stateAtAdversaryHalt execution generated =
            some output.occurrence
    | .noPair _ _ =>
        firstGeneratedPairOccurrenceInFrozenQ1
          source.origin.firstRun.stateAtAdversaryHalt execution generated =
            none := by
  cases outcome with
  | atomic output operational =>
      rcases operational with
        ⟨_tape, _identity, _q1, occurrence, _rest⟩
      exact occurrence
  | noPair output operational =>
      exact operational.1.2.2.2.1

def ReplayBranchOutcome.tapeIdentity
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration} :
    ReplayBranchOutcome source execution generated configuration → TapeIdentity
  | .atomic output _ => output.tapeIdentity
  | .noPair output _ => output.tapeIdentity

def ReplayBranchOutcome.q1
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration} :
    ReplayBranchOutcome source execution generated configuration → List QueryRecord
  | .atomic output _ => output.q1
  | .noPair output _ => output.q1

def ReplayBranchOutcome.resources
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    {source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result}
    {execution : ConcreteFirstExecution table dag.tape}
    {generated : GeneratedReplayPrefix dag}
    {configuration : AtomicPairReplayConfiguration} :
    ReplayBranchOutcome source execution generated configuration → ResourceUse
  | .atomic output _ => output.resources
  | .noPair output _ => output.resources

theorem dispatch_success_preserves_same_tape_q1_and_budget
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (outcome : ReplayBranchOutcome source execution generated configuration)
    (success : dispatchGeneratedReplayBranch source execution generated
      configuration = .ok outcome) :
    outcome.tapeIdentity = source.origin.capability.tapeIdentity ∧
      source.origin.capability.tapeIdentity =
        source.origin.firstRun.tapeIdentity ∧
      outcome.q1 = source.origin.firstRun.q1 ∧
      WithinBudget outcome.resources configuration.budget := by
  cases outcome with
  | atomic output operational =>
      rcases operational with
        ⟨tape, identity, q1, _occurrence, _split, _beforeFresh, _chosen,
          _actor, _pending, _classified, _pendingHalf, _assigned, _prefix,
          _paused, _residual, _trace, _freshOutput, _freshAdvance, _distinct,
          _programmingOrder, _programmed, _replay, _pendingQuery, _returned,
          _initialHistory, _replayHistory, _prefixSteps, _positive, _fuel,
          _resources, budget⟩
      exact ⟨tape, identity, q1, budget⟩
  | noPair output operational =>
      rcases operational with ⟨exactOutput, budget⟩
      exact ⟨exactOutput.1, exactOutput.2.1, exactOutput.2.2.1, budget⟩

theorem dispatch_success_relates_complete_seen_bound_state
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (outcome : ReplayBranchOutcome source execution generated configuration)
    (success : dispatchGeneratedReplayBranch source execution generated
      configuration = .ok outcome) :
    let restoration := concreteRestoration execution generated
    IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot execution.interactiveState ∧
      NonemptyVerifierHistory execution.interactiveState ∧
      restoration.snapshot.bindings =
        FixedBindings.ofContext dag.tape.messages.context ∧
      restoration.oracleTable = table ∧
      restoration.deployedTape = dag.tape := by
  let restoration := concreteRestoration execution generated
  exact ⟨restoration_snapshot_is_complete restoration,
    restoration_snapshot_is_previously_seen restoration,
    restoration_first_run_history_is_nonempty restoration,
    restoration_preserves_fixed_bindings restoration,
    restoration_retains_same_oracle_table restoration,
    restoration_retains_same_deployed_tape restoration⟩

#print axioms exact_no_pair_replay_exists
#print axioms constructNoPairReplay
#print axioms dispatchGeneratedReplayBranch
#print axioms generated_pair_occurrence_is_some_or_none
#print axioms dispatch_success_classifies_branch
#print axioms dispatch_success_preserves_same_tape_q1_and_budget
#print axioms dispatch_success_relates_complete_seen_bound_state

end

end AspisK1.V7Tag73ReplayBranchDispatcher
