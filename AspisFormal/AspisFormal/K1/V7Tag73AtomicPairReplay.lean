import AspisFormal.K1.V7Tag73AtomicPairFork
import AspisFormal.K1.V7FsStateRestorationCoupling
import AspisFormal.K1.V7Tag73ConcreteKnowledgeInsertion

/-!
# Executable same-tape replay at a Tag-73 atomic squeeze pair

This module replays the exact frozen-Q1 prefix before the first occurrence of
either call of a generated squeeze pair.  Both distinct inputs must be fresh.
The construction then programs both answers in an explicit order and resumes
the original pending query, so an output-first or advance-first occurrence
receives its corresponding assigned answer.

All failures are operational data.  There is no probability bound, acceptance
premise, extraction conclusion, abstract restore function, or trace-cover
field here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73AtomicPairReplay

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73ConcreteStateRestoration
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

inductive PairProgrammingOrder where
  | outputThenAdvance
  | advanceThenOutput
  deriving DecidableEq, Repr

def otherHalf : SqueezeHalf → SqueezeHalf
  | .output => .advance
  | .advance => .output

structure AtomicPairReplayConfiguration where
  forkOutput : ShaOutput
  forkAdvance : ShaOutput
  programmingOrder : PairProgrammingOrder
  postForkController : AdaptiveController
  oracleLimits : OracleLimits
  replayFuel : Nat
  firstRunUse : ResourceUse
  budget : ResourceBudget

def assignedPairOutput (configuration : AtomicPairReplayConfiguration) :
    SqueezeHalf → ShaOutput
  | .output => configuration.forkOutput
  | .advance => configuration.forkAdvance

def orderedPairHalves : PairProgrammingOrder → List SqueezeHalf
  | .outputThenAdvance => [.output, .advance]
  | .advanceThenOutput => [.advance, .output]

inductive AtomicPairReplayFailure where
  | missingPairOccurrence
  | replayEndedBeforePair
  | replayDidNotReachChosenInput
  | recordedPrefixMismatch
  | pairInputsAliased
  | inputConflict (half : SqueezeHalf)
  | programmingAbort (half : SqueezeHalf) (reason : OracleAbort)
  | timeout
  | replayAbort (reason : OracleAbort)
  | resourceBudget
  deriving DecidableEq, Repr

structure PairProgrammingResult where
  afterFirst : OracleState
  afterBoth : OracleState

noncomputable def programmingForHalf
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (half : SqueezeHalf) : Programming where
  input := generatedPairInput execution generated half
  output := assignedPairOutput configuration half

noncomputable def programPairInOrder
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (firstHalf secondHalf : SqueezeHalf) (state : OracleState) :
    Except AtomicPairReplayFailure PairProgrammingResult :=
  match programOracle configuration.oracleLimits .extractorReplay state
      (programmingForHalf execution generated configuration firstHalf) with
  | .error reason => .error (.programmingAbort firstHalf reason)
  | .ok afterFirst =>
      match programOracle configuration.oracleLimits .extractorReplay
          afterFirst
          (programmingForHalf execution generated configuration secondHalf) with
      | .error reason => .error (.programmingAbort secondHalf reason)
      | .ok afterBoth => .ok ⟨afterFirst, afterBoth⟩

/-- Program both pair entries.  Freshness is checked for both inputs before
the first insertion, and the insertion order is part of the configuration. -/
noncomputable def programAtomicPair
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (state : OracleState) :
    Except AtomicPairReplayFailure PairProgrammingResult :=
  let outputInput := generatedPairInput execution generated .output
  let advanceInput := generatedPairInput execution generated .advance
  if outputInput = advanceInput then
    .error .pairInputsAliased
  else
    match lookupEntry state outputInput with
    | some _ => .error (.inputConflict .output)
    | none =>
        match lookupEntry state advanceInput with
        | some _ => .error (.inputConflict .advance)
        | none =>
            match configuration.programmingOrder with
            | .outputThenAdvance => programPairInOrder execution generated
                configuration .output .advance state
            | .advanceThenOutput => programPairInOrder execution generated
                configuration .advance .output state

noncomputable def halfForPairInput
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (input : ShaInput) : Option SqueezeHalf :=
  if input = generatedPairInput execution generated .output then
    some .output
  else if input = generatedPairInput execution generated .advance then
    some .advance
  else none

structure AtomicPairReplayOutput
    (TapeIdentity Statement Proof Result : Type*) where
  tapeIdentity : TapeIdentity
  q1 : List QueryRecord
  occurrence : PairOccurrenceSplit
  chosenHalf : SqueezeHalf
  prefixRun : PrefixRun Result
  residualProgram : OracleMachine Result
  pendingInput : ShaInput
  pendingContinuation : ShaOutput → OracleMachine Result
  assignedPendingOutput : ShaOutput
  programming : PairProgrammingResult
  replayRun : MachineRun Result
  returned : Result
  resources : ResourceUse

/-- `runtimeSteps` counts executed `OracleMachine` query transitions.  The two
table-programming operations are not silently added to that counter: they are
accounted exactly and separately by the `programmedPoints` field and the
two-record theorem below. -/
def atomicPairResourceUse (firstRunUse : ResourceUse)
    (prefixSteps replaySteps : Nat) (finalOracle : OracleState) : ResourceUse :=
  couplingResourceUse firstRunUse prefixSteps replaySteps finalOracle

noncomputable def programmingRecordForHalf
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (half : SqueezeHalf) : ProgrammingRecord where
  input := generatedPairInput execution generated half
  output := assignedPairOutput configuration half
  actor := .extractorReplay

noncomputable def orderedProgrammingRecords
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration) :
    List ProgrammingRecord :=
  (orderedPairHalves configuration.programmingOrder).map
    (programmingRecordForHalf execution generated configuration)

/-- Every conjunct is a directly checkable execution/history/resource fact.
It contains no acceptance, witness or probability conclusion. -/
def IsOperationalAtomicPairReplay
    {TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output : AtomicPairReplayOutput TapeIdentity Statement Proof Result) : Prop :=
  output.tapeIdentity = origin.capability.tapeIdentity ∧
  origin.capability.tapeIdentity = origin.firstRun.tapeIdentity ∧
  output.q1 = origin.firstRun.q1 ∧
  firstGeneratedPairOccurrenceInFrozenQ1
      origin.firstRun.stateAtAdversaryHalt execution generated =
    some output.occurrence ∧
  output.q1 = output.occurrence.before ++
    output.occurrence.chosen :: output.occurrence.after ∧
  (∀ prior ∈ output.occurrence.before,
    prior.input ≠ generatedPairInput execution generated .output ∧
    prior.input ≠ generatedPairInput execution generated .advance) ∧
  (output.occurrence.chosen.input =
      generatedPairInput execution generated .output ∨
    output.occurrence.chosen.input =
      generatedPairInput execution generated .advance) ∧
  output.occurrence.chosen.actor = .adversary ∧
  output.pendingInput = output.occurrence.chosen.input ∧
  halfForPairInput execution generated output.pendingInput =
    some output.chosenHalf ∧
  output.pendingInput = generatedPairInput execution generated output.chosenHalf ∧
  output.assignedPendingOutput =
    assignedPairOutput configuration output.chosenHalf ∧
  output.prefixRun = AspisK1.V7FsStateRestorationCoupling.runPrefix
    (recordedPrefixController origin.initialOracle.history.length
      output.occurrence.before)
    configuration.oracleLimits .extractorReplay output.occurrence.before.length
    origin.initialOracle (origin.capability.start origin.observation) ∧
  output.prefixRun.halt = .paused output.residualProgram ∧
  output.residualProgram =
    .query output.pendingInput output.pendingContinuation ∧
  queryAnswerTrace
      (historySince origin.initialOracle output.prefixRun.oracle) =
    queryAnswerTrace output.occurrence.before ∧
  lookupEntry output.prefixRun.oracle
      (generatedPairInput execution generated .output) = none ∧
  lookupEntry output.prefixRun.oracle
      (generatedPairInput execution generated .advance) = none ∧
  generatedPairInput execution generated .output ≠
    generatedPairInput execution generated .advance ∧
  output.programming.afterBoth.programmingHistory =
    output.prefixRun.oracle.programmingHistory ++
      orderedProgrammingRecords execution generated configuration ∧
  (∀ half : SqueezeHalf,
    (lookupEntry output.programming.afterBoth
      (generatedPairInput execution generated half)).map
        AspisK1.V7FsAokExperiment.TableEntry.output =
      some (assignedPairOutput configuration half)) ∧
  output.replayRun = runMachine configuration.postForkController
    configuration.oracleLimits .extractorReplay configuration.replayFuel
    output.programming.afterBoth
    (.query output.pendingInput output.pendingContinuation) ∧
  (∃ afterPendingQuery : OracleState,
    queryOracle configuration.postForkController configuration.oracleLimits
      .extractorReplay output.programming.afterBoth output.pendingInput =
        .ok (output.assignedPendingOutput, afterPendingQuery)) ∧
  output.replayRun.halt = .returned output.returned ∧
  origin.initialOracle.history <+: output.prefixRun.oracle.history ∧
  output.prefixRun.oracle.history <+: output.replayRun.oracle.history ∧
  output.prefixRun.steps = output.occurrence.before.length ∧
  0 < output.replayRun.steps ∧
  output.replayRun.steps ≤ configuration.replayFuel ∧
  output.resources = atomicPairResourceUse configuration.firstRunUse
    output.prefixRun.steps output.replayRun.steps output.replayRun.oracle ∧
  WithinBudget output.resources configuration.budget

private def branchReplayOutput
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result)
    (occurrence : PairOccurrenceSplit) (chosenHalf : SqueezeHalf)
    (prefixRun : PrefixRun Result) (residual : OracleMachine Result)
    (pendingInput : ShaInput)
    (pendingContinuation : ShaOutput → OracleMachine Result)
    (configuration : AtomicPairReplayConfiguration)
    (programming : PairProgrammingResult) (replayRun : MachineRun Result)
    (result : Result) :
    AtomicPairReplayOutput TapeIdentity Statement Proof Result :=
  { tapeIdentity := origin.capability.tapeIdentity
    q1 := origin.firstRun.q1
    occurrence := occurrence
    chosenHalf := chosenHalf
    prefixRun := prefixRun
    residualProgram := residual
    pendingInput := pendingInput
    pendingContinuation := pendingContinuation
    assignedPendingOutput := assignedPairOutput configuration chosenHalf
    programming := programming
    replayRun := replayRun
    returned := result
    resources := atomicPairResourceUse configuration.firstRunUse
      prefixRun.steps replayRun.steps replayRun.oracle }

/-! ## Local operational lemmas -/

theorem half_for_output_input
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    halfForPairInput execution generated
      (generatedPairInput execution generated .output) = some .output := by
  simp [halfForPairInput]

theorem half_for_advance_input
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    halfForPairInput execution generated
      (generatedPairInput execution generated .advance) = some .advance := by
  unfold halfForPairInput
  rw [if_neg (Ne.symm
    (generated_pair_inputs_are_distinct execution generated))]
  simp

theorem half_for_pair_input_some_is_exact
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (input : ShaInput) (half : SqueezeHalf)
    (classified : halfForPairInput execution generated input = some half) :
    input = generatedPairInput execution generated half := by
  cases half with
  | output =>
      unfold halfForPairInput at classified
      split at classified
      next hit => exact hit
      next _ =>
        split at classified <;> contradiction
  | advance =>
      unfold halfForPairInput at classified
      split at classified
      next _ => contradiction
      next _ =>
        split at classified
        next hit => exact hit
        next _ => contradiction

theorem atomic_pair_resource_increments_exact
    (firstRunUse : ResourceUse) (prefixSteps replaySteps : Nat)
    (finalOracle : OracleState) :
    (atomicPairResourceUse firstRunUse prefixSteps replaySteps finalOracle).extractorOracleCalls =
        firstRunUse.extractorOracleCalls + prefixSteps + replaySteps ∧
      (atomicPairResourceUse firstRunUse prefixSteps replaySteps finalOracle).restartCount =
        firstRunUse.restartCount + 1 ∧
      (atomicPairResourceUse firstRunUse prefixSteps replaySteps finalOracle).runtimeSteps =
        firstRunUse.runtimeSteps + prefixSteps + replaySteps ∧
      (atomicPairResourceUse firstRunUse prefixSteps replaySteps finalOracle).programmedPoints =
        finalOracle.programmingHistory.length := by
  exact ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem ordered_pair_halves_length (order : PairProgrammingOrder) :
    (orderedPairHalves order).length = 2 := by
  cases order <;> rfl

@[simp] theorem ordered_programming_records_length
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration) :
    (orderedProgrammingRecords execution generated configuration).length = 2 := by
  simpa [orderedProgrammingRecords] using
    ordered_pair_halves_length configuration.programmingOrder

private theorem table_find_append_preserves_some
    (table suffix : List AspisK1.V7FsAokExperiment.TableEntry)
    (input : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (found : table.find? (fun candidate => candidate.input = input) =
      some entry) :
    (table ++ suffix).find? (fun candidate => candidate.input = input) =
      some entry := by
  induction table with
  | nil => simp at found
  | cons head tail ih =>
      by_cases hit : head.input = input
      · simpa [hit] using found
      · have tailFound :
            tail.find? (fun candidate => candidate.input = input) =
              some entry := by
          simpa [hit] using found
        simpa [hit] using ih tailFound

private theorem table_find_append_fresh
    (table : List AspisK1.V7FsAokExperiment.TableEntry)
    (input : ShaInput) (output : ShaOutput)
    (missing : table.find? (fun candidate => candidate.input = input) = none) :
    (table ++
      [({ input := input, output := output, source := .programmed } :
        AspisK1.V7FsAokExperiment.TableEntry)]).find?
        (fun candidate => candidate.input = input) =
      some ({ input := input, output := output, source := .programmed } :
        AspisK1.V7FsAokExperiment.TableEntry) := by
  induction table with
  | nil => simp
  | cons head tail ih =>
      by_cases hit : head.input = input
      · simp [hit] at missing
      · have tailMissing :
            tail.find? (fun candidate => candidate.input = input) = none := by
          simpa [hit] using missing
        simpa [hit] using ih tailMissing

theorem program_oracle_success_exact
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (programming : Programming)
    (success : programOracle limits actor state programming = .ok nextState) :
    nextState.history = state.history ∧
      nextState.programmingHistory = state.programmingHistory ++
        [({ input := programming.input
            output := programming.output
            actor := actor } : ProgrammingRecord)] ∧
      nextState.table = state.table ++
        [({ input := programming.input
            output := programming.output
            source := .programmed } :
          AspisK1.V7FsAokExperiment.TableEntry)] ∧
      (lookupEntry nextState programming.input).map
          AspisK1.V7FsAokExperiment.TableEntry.output =
        some programming.output := by
  unfold programOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next _ => contradiction
    next fresh =>
      simp only [Except.ok.injEq] at success
      subst nextState
      refine ⟨rfl, rfl, rfl, ?_⟩
      have missing : lookupEntry state programming.input = none := by
        cases found : lookupEntry state programming.input with
        | none => rfl
        | some entry => simp [found] at fresh
      unfold lookupEntry at missing ⊢
      rw [table_find_append_fresh state.table programming.input
        programming.output missing]
      rfl

theorem program_oracle_success_preserves_lookup_answer
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (programming : Programming)
    (success : programOracle limits actor state programming = .ok nextState)
    (input : ShaInput) (output : ShaOutput)
    (found : (lookupEntry state input).map
      AspisK1.V7FsAokExperiment.TableEntry.output = some output) :
    (lookupEntry nextState input).map
      AspisK1.V7FsAokExperiment.TableEntry.output = some output := by
  have exactState := program_oracle_success_exact limits actor state nextState
    programming success
  cases selected : lookupEntry state input with
  | none => simp [selected] at found
  | some entry =>
      have entryOutput : entry.output = output := by
        simpa [selected] using found
      have preserved :
          (nextState.table.find? fun candidate => candidate.input = input) =
            some entry := by
        rw [exactState.2.2.1]
        exact table_find_append_preserves_some state.table _ input entry
          (by simpa [lookupEntry] using selected)
      unfold lookupEntry
      rw [preserved]
      simpa [entryOutput]

theorem program_pair_in_order_success_exact
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (firstHalf secondHalf : SqueezeHalf)
    (state : OracleState) (result : PairProgrammingResult)
    (success : programPairInOrder execution generated configuration
      firstHalf secondHalf state =
      .ok result) :
    result.afterBoth.history = state.history ∧
      result.afterBoth.programmingHistory = state.programmingHistory ++
        [programmingRecordForHalf execution generated configuration firstHalf,
          programmingRecordForHalf execution generated configuration secondHalf] ∧
      (lookupEntry result.afterBoth
        (generatedPairInput execution generated firstHalf)).map
          AspisK1.V7FsAokExperiment.TableEntry.output =
        some (assignedPairOutput configuration firstHalf) ∧
      (lookupEntry result.afterBoth
        (generatedPairInput execution generated secondHalf)).map
          AspisK1.V7FsAokExperiment.TableEntry.output =
        some (assignedPairOutput configuration secondHalf) := by
  unfold programPairInOrder at success
  cases firstProgram : programOracle configuration.oracleLimits
      .extractorReplay state
      (programmingForHalf execution generated configuration firstHalf) with
  | error reason =>
      simp only [firstProgram] at success
      cases success
  | ok afterFirst =>
      cases secondProgram : programOracle configuration.oracleLimits
          .extractorReplay afterFirst
          (programmingForHalf execution generated configuration secondHalf) with
      | error reason =>
          simp only [firstProgram, secondProgram] at success
          cases success
      | ok afterBoth =>
          simp only [firstProgram, secondProgram, Except.ok.injEq] at success
          subst result
          have firstExact := program_oracle_success_exact
            configuration.oracleLimits .extractorReplay state afterFirst
              (programmingForHalf execution generated configuration firstHalf)
                firstProgram
          have secondExact := program_oracle_success_exact
            configuration.oracleLimits .extractorReplay afterFirst afterBoth
              (programmingForHalf execution generated configuration secondHalf)
                secondProgram
          refine ⟨secondExact.1.trans firstExact.1, ?_, ?_, ?_⟩
          · rw [secondExact.2.1, firstExact.2.1]
            simp [programmingRecordForHalf, programmingForHalf,
              List.append_assoc]
          · simpa [programmingForHalf, assignedPairOutput] using
              program_oracle_success_preserves_lookup_answer
                configuration.oracleLimits .extractorReplay afterFirst afterBoth
                (programmingForHalf execution generated configuration secondHalf)
                secondProgram
                (generatedPairInput execution generated firstHalf)
                (assignedPairOutput configuration firstHalf)
                (by simpa [programmingForHalf, assignedPairOutput] using
                  firstExact.2.2.2)
          · simpa [programmingForHalf, assignedPairOutput] using
              secondExact.2.2.2

theorem program_atomic_pair_success_exact
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (state : OracleState) (result : PairProgrammingResult)
    (success : programAtomicPair execution generated configuration state =
      .ok result) :
    lookupEntry state (generatedPairInput execution generated .output) = none ∧
      lookupEntry state (generatedPairInput execution generated .advance) = none ∧
      result.afterBoth.history = state.history ∧
      result.afterBoth.programmingHistory = state.programmingHistory ++
        orderedProgrammingRecords execution generated configuration ∧
      ∀ half : SqueezeHalf,
        (lookupEntry result.afterBoth
          (generatedPairInput execution generated half)).map
            AspisK1.V7FsAokExperiment.TableEntry.output =
          some (assignedPairOutput configuration half) := by
  have distinct := generated_pair_inputs_are_distinct execution generated
  simp only [programAtomicPair, distinct, if_false] at success
  cases outputFound : lookupEntry state
      (generatedPairInput execution generated .output) with
  | some entry =>
      simp only [outputFound] at success
      cases success
  | none =>
      rw [outputFound] at success
      cases advanceFound : lookupEntry state
          (generatedPairInput execution generated .advance) with
      | some entry =>
          simp only [advanceFound] at success
          cases success
      | none =>
          rw [advanceFound] at success
          cases order : configuration.programmingOrder with
          | outputThenAdvance =>
              have sequential := program_pair_in_order_success_exact execution
                generated configuration .output .advance state result
                (by simpa [order] using success)
              refine ⟨rfl, rfl, sequential.1, ?_, ?_⟩
              · simpa [orderedProgrammingRecords, orderedPairHalves,
                  order] using sequential.2.1
              · intro half
                cases half with
                | output => exact sequential.2.2.1
                | advance => exact sequential.2.2.2
          | advanceThenOutput =>
              have sequential := program_pair_in_order_success_exact execution
                generated configuration .advance .output state result
                (by simpa [order] using success)
              refine ⟨rfl, rfl, sequential.1, ?_, ?_⟩
              · simpa [orderedProgrammingRecords, orderedPairHalves,
                  order] using sequential.2.1
              · intro half
                cases half with
                | output => exact sequential.2.2.2
                | advance => exact sequential.2.2.1

theorem run_prefix_paused_steps_eq_fuel
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program residual : OracleMachine Result)
    (paused : (AspisK1.V7FsStateRestorationCoupling.runPrefix
      controller limits actor fuel state program).halt =
      .paused residual) :
    (AspisK1.V7FsStateRestorationCoupling.runPrefix
      controller limits actor fuel state program).steps = fuel := by
  induction fuel generalizing state program residual with
  | zero => simp [AspisK1.V7FsStateRestorationCoupling.runPrefix]
  | succ fuel ih =>
      cases program with
      | pure result =>
          simp [AspisK1.V7FsStateRestorationCoupling.runPrefix] at paused
      | abort reason =>
          simp [AspisK1.V7FsStateRestorationCoupling.runPrefix] at paused
      | query input next =>
          cases queried : queryOracle controller limits actor state input with
          | error reason =>
              simp [AspisK1.V7FsStateRestorationCoupling.runPrefix, queried]
                at paused
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have recursivePaused :
                  (AspisK1.V7FsStateRestorationCoupling.runPrefix
                    controller limits actor fuel nextState
                      (next output)).halt = .paused residual := by
                simpa [AspisK1.V7FsStateRestorationCoupling.runPrefix, queried]
                  using paused
              have steps := ih nextState (next output) residual recursivePaused
              simpa [AspisK1.V7FsStateRestorationCoupling.runPrefix, queried,
                steps]

theorem run_machine_returned_query_has_positive_steps
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (input : ShaInput) (next : ShaOutput → OracleMachine Result)
    (result : Result)
    (returned : (runMachine controller limits actor fuel state
      (.query input next)).halt = .returned result) :
    0 < (runMachine controller limits actor fuel state
      (.query input next)).steps := by
  cases fuel with
  | zero => simp [runMachine] at returned
  | succ fuel =>
      cases queried : queryOracle controller limits actor state input with
      | error reason => simp [runMachine, queried] at returned
      | ok pair =>
          rcases pair with ⟨output, nextState⟩
          simp [runMachine, queried]

theorem query_oracle_success_preserves_programming_history
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    nextState.programmingHistory = state.programmingHistory := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      rfl
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          rfl

theorem run_machine_preserves_programming_history
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    (runMachine controller limits actor fuel state program).oracle.programmingHistory =
      state.programmingHistory := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> rfl
  | succ fuel ih =>
      cases program with
      | pure result => rfl
      | abort reason => rfl
      | query input next =>
          cases queried : queryOracle controller limits actor state input with
          | error reason => simp [runMachine, queried]
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have queryPreserves :=
                query_oracle_success_preserves_programming_history
                  controller limits actor state nextState input output queried
              have tailPreserves := ih nextState (next output)
              simpa only [runMachine, queried] using
                tailPreserves.trans queryPreserves

theorem atomic_run_machine_steps_le_fuel
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    (runMachine controller limits actor fuel state program).steps ≤ fuel := by
  induction fuel generalizing state program with
  | zero => cases program <;> simp [runMachine]
  | succ fuel ih =>
      cases program with
      | pure result => simp [runMachine]
      | abort reason => simp [runMachine]
      | query input next =>
          simp only [runMachine]
          cases queried : queryOracle controller limits actor state input with
          | error reason => simp
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have tail := ih nextState (next output)
              change
                (runMachine controller limits actor fuel nextState
                    (next output)).steps + 1 ≤ fuel + 1
              omega

theorem run_machine_returned_query_exposes_first_call
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (input : ShaInput) (next : ShaOutput → OracleMachine Result)
    (result : Result)
    (returned : (runMachine controller limits actor fuel state
      (.query input next)).halt = .returned result) :
    ∃ output : ShaOutput, ∃ nextState : OracleState,
      queryOracle controller limits actor state input = .ok (output, nextState) := by
  cases fuel with
  | zero => simp [runMachine] at returned
  | succ fuel =>
      cases queried : queryOracle controller limits actor state input with
      | error reason => simp [runMachine, queried] at returned
      | ok pair =>
          rcases pair with ⟨output, nextState⟩
          exact ⟨output, nextState, by simpa only using queried⟩

theorem query_oracle_success_uses_cached_lookup_answer
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (actual assigned : ShaOutput)
    (found : (lookupEntry state input).map
      AspisK1.V7FsAokExperiment.TableEntry.output = some assigned)
    (success : queryOracle controller limits actor state input =
      .ok (actual, nextState)) :
    actual = assigned := by
  cases selected : lookupEntry state input with
  | none => simp [selected] at found
  | some entry =>
      have entryOutput : entry.output = assigned := by
        simpa [selected] using found
      unfold queryOracle at success
      split at success <;> try contradiction
      next _ =>
        rw [selected] at success
        simp only [Except.ok.injEq, Prod.mk.injEq] at success
        exact success.1.symm.trans entryOutput

private theorem branch_replay_output_is_operational
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (occurrence : PairOccurrenceSplit) (chosenHalf : SqueezeHalf)
    (prefixRun : PrefixRun Result) (residual : OracleMachine Result)
    (pendingInput : ShaInput)
    (pendingContinuation : ShaOutput → OracleMachine Result)
    (programming : PairProgrammingResult) (replayRun : MachineRun Result)
    (result : Result)
    (occurrenceFound : firstGeneratedPairOccurrenceInFrozenQ1
      source.origin.firstRun.stateAtAdversaryHalt execution generated =
        some occurrence)
    (prefixDefinition : prefixRun =
      AspisK1.V7FsStateRestorationCoupling.runPrefix
        (recordedPrefixController source.origin.initialOracle.history.length
          occurrence.before)
        configuration.oracleLimits .extractorReplay occurrence.before.length
        source.origin.initialOracle
        (source.origin.capability.start source.origin.observation))
    (paused : prefixRun.halt = .paused residual)
    (residualQuery : residual = .query pendingInput pendingContinuation)
    (pendingChosen : pendingInput = occurrence.chosen.input)
    (trace : queryAnswerTrace
      (historySince source.origin.initialOracle prefixRun.oracle) =
        queryAnswerTrace occurrence.before)
    (halfClassification : halfForPairInput execution generated pendingInput =
      some chosenHalf)
    (programmingSuccess : programAtomicPair execution generated configuration
      prefixRun.oracle = .ok programming)
    (replayDefinition : replayRun = runMachine
      configuration.postForkController configuration.oracleLimits
      .extractorReplay configuration.replayFuel programming.afterBoth
      (.query pendingInput pendingContinuation))
    (replayReturned : replayRun.halt = .returned result)
    (withinBudget : WithinBudget
      (atomicPairResourceUse configuration.firstRunUse prefixRun.steps
        replayRun.steps replayRun.oracle) configuration.budget) :
    IsOperationalAtomicPairReplay source.origin execution generated
      configuration
      (branchReplayOutput source.origin occurrence chosenHalf prefixRun residual
        pendingInput pendingContinuation configuration programming replayRun
          result) := by
  have occurrenceExact :=
    first_generated_pair_occurrence_in_frozen_q1_is_exact
      source.origin.firstRun.stateAtAdversaryHalt execution generated occurrence
        occurrenceFound
  rcases occurrenceExact with
    ⟨q1Split, beforeFresh, chosenInput, chosenActor⟩
  have pairExact := program_atomic_pair_success_exact execution generated
    configuration prefixRun.oracle programming programmingSuccess
  rcases pairExact with
    ⟨freshOutput, freshAdvance, programmedHistory, programmingOrder,
      programmed⟩
  have pendingHalf := half_for_pair_input_some_is_exact execution generated
    pendingInput chosenHalf halfClassification
  have initialHistory := prefix_run_history_is_preserved
    (recordedPrefixController source.origin.initialOracle.history.length
      occurrence.before)
    configuration.oracleLimits .extractorReplay occurrence.before.length
    source.origin.initialOracle
    (source.origin.capability.start source.origin.observation)
  rw [← prefixDefinition] at initialHistory
  have postforkHistory := postfork_run_history_is_preserved
    configuration.postForkController configuration.oracleLimits
      .extractorReplay configuration.replayFuel programming.afterBoth
      (.query pendingInput pendingContinuation)
  rw [← replayDefinition] at postforkHistory
  have replayHistory : prefixRun.oracle.history <+: replayRun.oracle.history := by
    rw [← programmedHistory]
    exact postforkHistory
  have prefixPaused :
      (AspisK1.V7FsStateRestorationCoupling.runPrefix
        (recordedPrefixController source.origin.initialOracle.history.length
          occurrence.before)
        configuration.oracleLimits .extractorReplay occurrence.before.length
        source.origin.initialOracle
        (source.origin.capability.start source.origin.observation)).halt =
          .paused residual := by
    rw [← prefixDefinition]
    exact paused
  have prefixSteps := run_prefix_paused_steps_eq_fuel
    (recordedPrefixController source.origin.initialOracle.history.length
      occurrence.before)
    configuration.oracleLimits .extractorReplay occurrence.before.length
    source.origin.initialOracle
    (source.origin.capability.start source.origin.observation) residual
      prefixPaused
  rw [← prefixDefinition] at prefixSteps
  have returnedRun :
      (runMachine configuration.postForkController configuration.oracleLimits
        .extractorReplay configuration.replayFuel programming.afterBoth
        (.query pendingInput pendingContinuation)).halt = .returned result := by
    rw [← replayDefinition]
    exact replayReturned
  have replayPositive := run_machine_returned_query_has_positive_steps
    configuration.postForkController configuration.oracleLimits
      .extractorReplay configuration.replayFuel programming.afterBoth
      pendingInput pendingContinuation result returnedRun
  have replayFuelBound := atomic_run_machine_steps_le_fuel
    configuration.postForkController configuration.oracleLimits
      .extractorReplay configuration.replayFuel programming.afterBoth
      (.query pendingInput pendingContinuation)
  rw [← replayDefinition] at replayPositive replayFuelBound
  obtain ⟨actualOutput, afterPendingQuery, pendingQuery⟩ :=
    run_machine_returned_query_exposes_first_call
      configuration.postForkController configuration.oracleLimits
        .extractorReplay configuration.replayFuel programming.afterBoth
        pendingInput pendingContinuation result returnedRun
  have pendingLookup :
      (lookupEntry programming.afterBoth pendingInput).map
          AspisK1.V7FsAokExperiment.TableEntry.output =
        some (assignedPairOutput configuration chosenHalf) := by
    rw [pendingHalf]
    exact programmed chosenHalf
  have actualAssigned := query_oracle_success_uses_cached_lookup_answer
    configuration.postForkController configuration.oracleLimits
      .extractorReplay programming.afterBoth afterPendingQuery pendingInput
      actualOutput (assignedPairOutput configuration chosenHalf) pendingLookup
      pendingQuery
  have assignedPendingQuery :
      queryOracle configuration.postForkController configuration.oracleLimits
        .extractorReplay programming.afterBoth pendingInput =
          .ok (assignedPairOutput configuration chosenHalf,
            afterPendingQuery) := by
    rw [← actualAssigned]
    exact pendingQuery
  unfold branchReplayOutput
  refine ⟨rfl, (source_origin_identity source).symm, rfl, occurrenceFound,
    ?_, beforeFresh, chosenInput, chosenActor, pendingChosen,
    halfClassification, pendingHalf, rfl, prefixDefinition, paused,
    residualQuery, trace, freshOutput, freshAdvance,
    generated_pair_inputs_are_distinct execution generated,
    programmingOrder, programmed, replayDefinition,
    ⟨afterPendingQuery, assignedPendingQuery⟩, replayReturned,
    initialHistory, replayHistory, prefixSteps,
    replayPositive, replayFuelBound,
    rfl, withinBudget⟩
  change source.origin.firstRun.q1 =
    occurrence.before ++ occurrence.chosen :: occurrence.after
  simpa only [FirstRun.q1] using q1Split

/-- Direct source-constructed replay map.  Every successful branch carries a
proof derived from the concrete occurrence, prefix, programming, and replay
equations; there is no whole-conclusion test or invariant-check failure. -/
noncomputable def constructAtomicPairReplay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration) :
    Except AtomicPairReplayFailure
      {output : AtomicPairReplayOutput TapeIdentity Statement Proof Result //
        IsOperationalAtomicPairReplay source.origin execution generated
          configuration output} := by
  classical
  exact match occurrenceFound : firstGeneratedPairOccurrenceInFrozenQ1
      source.origin.firstRun.stateAtAdversaryHalt execution generated with
  | none => .error .missingPairOccurrence
  | some occurrence =>
      let prefixRun := AspisK1.V7FsStateRestorationCoupling.runPrefix
        (recordedPrefixController source.origin.initialOracle.history.length
          occurrence.before)
        configuration.oracleLimits .extractorReplay occurrence.before.length
        source.origin.initialOracle
        (source.origin.capability.start source.origin.observation)
      match prefixHalt : prefixRun.halt with
      | .returned _ | .oracleAbort _ => .error .replayEndedBeforePair
      | .paused residual =>
          match residualShape : residual with
          | .pure _ | .abort _ => .error .replayEndedBeforePair
          | .query pendingInput next =>
              if pendingMismatch : pendingInput ≠ occurrence.chosen.input then
                .error .replayDidNotReachChosenInput
              else
                have pendingChosen : pendingInput = occurrence.chosen.input := by
                  exact Classical.byContradiction fun unequal =>
                    pendingMismatch unequal
                if traceMismatch : queryAnswerTrace
                    (historySince source.origin.initialOracle prefixRun.oracle) ≠
                      queryAnswerTrace occurrence.before then
                  .error .recordedPrefixMismatch
                else
                  have trace : queryAnswerTrace
                      (historySince source.origin.initialOracle prefixRun.oracle) =
                        queryAnswerTrace occurrence.before := by
                    exact Classical.byContradiction fun unequal =>
                      traceMismatch unequal
                  match halfClassification : halfForPairInput execution generated
                      pendingInput with
                  | none => .error .replayDidNotReachChosenInput
                  | some chosenHalf =>
                      match programmingSuccess : programAtomicPair execution
                          generated configuration prefixRun.oracle with
                      | .error reason => .error reason
                      | .ok programming =>
                          if configuration.replayFuel = 0 then
                            .error .timeout
                          else
                            let replayRun := runMachine
                              configuration.postForkController
                              configuration.oracleLimits .extractorReplay
                              configuration.replayFuel programming.afterBoth
                              (.query pendingInput next)
                            match replayHalt : replayRun.halt with
                            | .outOfFuel => .error .timeout
                            | .oracleAbort reason =>
                                .error (.replayAbort reason)
                            | .returned result =>
                                if budgetOk : WithinBudget
                                    (atomicPairResourceUse
                                      configuration.firstRunUse prefixRun.steps
                                      replayRun.steps replayRun.oracle)
                                    configuration.budget then
                                  let output := branchReplayOutput source.origin
                                    occurrence chosenHalf prefixRun residual
                                    pendingInput next configuration programming
                                    replayRun result
                                  have operational :=
                                    branch_replay_output_is_operational source
                                      execution generated configuration occurrence
                                      chosenHalf prefixRun residual pendingInput
                                      next programming replayRun result
                                      occurrenceFound rfl
                                      (by simpa [residualShape] using prefixHalt)
                                      residualShape
                                      pendingChosen trace halfClassification
                                      programmingSuccess rfl replayHalt budgetOk
                                  .ok ⟨output, operational⟩
                                else
                                  .error .resourceBudget

/-! ## Successful construction facts -/

theorem construct_atomic_pair_replay_success_is_operational
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement Proof Result //
        IsOperationalAtomicPairReplay source.origin execution generated configuration
          run})
    (success : constructAtomicPairReplay source execution generated
      configuration = .ok output) :
    IsOperationalAtomicPairReplay source.origin execution generated configuration
      output.1 := by
  exact output.2

theorem construct_atomic_pair_replay_success_preserves_origin_and_q1
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement Proof Result //
        IsOperationalAtomicPairReplay source.origin execution generated configuration
          run})
    (success : constructAtomicPairReplay source execution generated
      configuration = .ok output) :
    output.1.tapeIdentity = source.origin.capability.tapeIdentity ∧
      source.origin.capability.tapeIdentity = source.origin.firstRun.tapeIdentity ∧
      output.1.q1 = source.origin.firstRun.q1 ∧
      output.1.q1 = output.1.occurrence.before ++
        output.1.occurrence.chosen :: output.1.occurrence.after ∧
      output.1.occurrence.chosen.actor = .adversary := by
  have operational := output.2
  rcases operational with
    ⟨tape, identity, q1, occurrenceFound, split, beforeFresh, chosenInput,
      actor, pendingChosen, halfClassification, pendingHalf, assigned,
      prefixDefinition, paused, residual, trace, freshOutput, freshAdvance,
      distinct, programmingOrder, programmed, replayDefinition, pendingQuery,
      returned, initialHistory, replayHistory, prefixSteps, replaySteps,
      replayFuelBound, resources, withinBudget⟩
  exact ⟨tape, identity, q1, split, actor⟩

theorem construct_atomic_pair_replay_success_has_exact_prefix_and_resources
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement Proof Result //
        IsOperationalAtomicPairReplay source.origin execution generated configuration
          run})
    (success : constructAtomicPairReplay source execution generated
      configuration = .ok output) :
    queryAnswerTrace
        (historySince source.origin.initialOracle output.1.prefixRun.oracle) =
        queryAnswerTrace output.1.occurrence.before ∧
      output.1.prefixRun.steps = output.1.occurrence.before.length ∧
      0 < output.1.replayRun.steps ∧
      output.1.resources = atomicPairResourceUse configuration.firstRunUse
        output.1.prefixRun.steps output.1.replayRun.steps
          output.1.replayRun.oracle := by
  have operational := output.2
  rcases operational with
    ⟨tape, identity, q1, occurrenceFound, split, beforeFresh, chosenInput,
      actor, pendingChosen, halfClassification, pendingHalf, assigned,
      prefixDefinition, paused, residual, trace, freshOutput, freshAdvance,
      distinct, programmingOrder, programmed, replayDefinition, pendingQuery,
      returned, initialHistory, replayHistory, prefixSteps, replaySteps,
      replayFuelBound, resources, withinBudget⟩
  exact ⟨trace, prefixSteps, replaySteps, resources⟩

theorem construct_atomic_pair_replay_success_programs_both_and_resumes_assigned
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement Proof Result //
        IsOperationalAtomicPairReplay source.origin execution generated configuration
          run})
    (success : constructAtomicPairReplay source execution generated
      configuration = .ok output) :
    output.1.programming.afterBoth.programmingHistory =
        output.1.prefixRun.oracle.programmingHistory ++
          orderedProgrammingRecords execution generated configuration ∧
      (output.1.programming.afterBoth.programmingHistory.length =
        output.1.prefixRun.oracle.programmingHistory.length + 2) ∧
      (∀ half : SqueezeHalf,
        (lookupEntry output.1.programming.afterBoth
          (generatedPairInput execution generated half)).map
            AspisK1.V7FsAokExperiment.TableEntry.output =
          some (assignedPairOutput configuration half)) ∧
      output.1.pendingInput =
        generatedPairInput execution generated output.1.chosenHalf ∧
      output.1.assignedPendingOutput =
        assignedPairOutput configuration output.1.chosenHalf ∧
      (∃ afterPendingQuery : OracleState,
        queryOracle configuration.postForkController configuration.oracleLimits
          .extractorReplay output.1.programming.afterBoth
            output.1.pendingInput =
          .ok (output.1.assignedPendingOutput, afterPendingQuery)) ∧
      output.1.replayRun = runMachine configuration.postForkController
        configuration.oracleLimits .extractorReplay configuration.replayFuel
        output.1.programming.afterBoth
        (.query output.1.pendingInput output.1.pendingContinuation) := by
  have operational := output.2
  rcases operational with
    ⟨tape, identity, q1, occurrenceFound, split, beforeFresh, chosenInput,
      actor, pendingChosen, halfClassification, pendingHalf, assigned,
      prefixDefinition, paused, residual, trace, freshOutput, freshAdvance,
      distinct, programmingOrder, programmed, replayDefinition, pendingQuery,
      returned, initialHistory, replayHistory, prefixSteps, replaySteps,
      replayFuelBound, resources, withinBudget⟩
  have programmingLength :
      output.1.programming.afterBoth.programmingHistory.length =
        output.1.prefixRun.oracle.programmingHistory.length + 2 := by
    rw [programmingOrder, List.length_append,
      ordered_programming_records_length execution generated configuration]
  exact ⟨programmingOrder, programmingLength, programmed, pendingHalf,
    assigned, pendingQuery, replayDefinition⟩

theorem construct_atomic_pair_replay_success_has_exact_resource_increments
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement Proof Result //
        IsOperationalAtomicPairReplay source.origin execution generated configuration
          run})
    (success : constructAtomicPairReplay source execution generated
      configuration = .ok output) :
    output.1.resources.extractorOracleCalls =
        configuration.firstRunUse.extractorOracleCalls +
          output.1.occurrence.before.length + output.1.replayRun.steps ∧
      output.1.resources.restartCount =
        configuration.firstRunUse.restartCount + 1 ∧
      output.1.resources.runtimeSteps =
        configuration.firstRunUse.runtimeSteps +
          output.1.occurrence.before.length + output.1.replayRun.steps ∧
      output.1.resources.programmedPoints =
        output.1.prefixRun.oracle.programmingHistory.length + 2 ∧
      0 < output.1.replayRun.steps ∧
      output.1.replayRun.steps ≤ configuration.replayFuel ∧
      WithinBudget output.1.resources configuration.budget := by
  have operational := output.2
  rcases operational with
    ⟨tape, identity, q1, occurrenceFound, split, beforeFresh, chosenInput,
      actor, pendingChosen, halfClassification, pendingHalf, assigned,
      prefixDefinition, paused, residual, trace, freshOutput, freshAdvance,
      distinct, programmingOrder, programmed, replayDefinition, pendingQuery,
      returned, initialHistory, replayHistory, prefixSteps, replaySteps,
      replayFuelBound, resources, withinBudget⟩
  have increments := atomic_pair_resource_increments_exact
    configuration.firstRunUse output.1.prefixRun.steps output.1.replayRun.steps
      output.1.replayRun.oracle
  have programmingLength :
      output.1.programming.afterBoth.programmingHistory.length =
        output.1.prefixRun.oracle.programmingHistory.length + 2 := by
    rw [programmingOrder, List.length_append,
      ordered_programming_records_length execution generated configuration]
  have finalProgrammingHistory :
      output.1.replayRun.oracle.programmingHistory =
        output.1.programming.afterBoth.programmingHistory := by
    rw [replayDefinition]
    exact run_machine_preserves_programming_history
      configuration.postForkController configuration.oracleLimits
        .extractorReplay configuration.replayFuel
        output.1.programming.afterBoth
        (.query output.1.pendingInput output.1.pendingContinuation)
  rw [resources] at withinBudget ⊢
  refine ⟨?_, increments.2.1, ?_, ?_, replaySteps, replayFuelBound,
    withinBudget⟩
  · simpa [prefixSteps] using increments.1
  · simpa [prefixSteps] using increments.2.2.1
  · rw [increments.2.2.2, finalProgrammingHistory, programmingLength]

theorem construct_atomic_pair_replay_success_relates_complete_restoration
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement Proof Result //
        IsOperationalAtomicPairReplay source.origin execution generated configuration
          run})
    (success : constructAtomicPairReplay source execution generated
      configuration = .ok output) :
    let restoration := concreteRestoration execution generated
    firstGeneratedPairOccurrenceInFrozenQ1
        source.origin.firstRun.stateAtAdversaryHalt execution generated =
      some output.1.occurrence ∧
      restorationAtPairHalf execution generated output.1.chosenHalf =
        restoration ∧
      IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot
        restoration.sourceExecution.interactiveState ∧
      NonemptyVerifierHistory restoration.sourceExecution.interactiveState ∧
      restoration.snapshot.bindings.programId =
        dag.tape.messages.context.programId ∧
      restoration.snapshot.bindings.releaseBinding =
        dag.tape.messages.context.releaseBinding ∧
      restoration.snapshot.bindings.statementDigest =
        dag.tape.messages.context.statementDigest ∧
      restoration.snapshot.bindings.attemptId =
        dag.tape.messages.context.attemptId ∧
      restoration.snapshot.bindings.proofAccountId =
        dag.tape.messages.context.attemptId := by
  have operational := output.2
  rcases operational with
    ⟨tape, identity, q1, occurrenceFound, split, beforeFresh, chosenInput,
      actor, pendingChosen, halfClassification, pendingHalf, assigned,
      prefixDefinition, paused, residual, trace, freshOutput, freshAdvance,
      distinct, programmingOrder, programmed, replayDefinition, pendingQuery,
      returned, initialHistory, replayHistory, prefixSteps, replaySteps,
      replayFuelBound, resources, withinBudget⟩
  let restoration := concreteRestoration execution generated
  have bindings :=
    restoration_preserves_program_release_statement_attempt_account restoration
  exact ⟨occurrenceFound, rfl, restoration_snapshot_is_complete restoration,
    restoration_snapshot_is_previously_seen restoration,
    restoration_first_run_history_is_nonempty restoration,
    bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2.1,
    bindings.2.2.2.2⟩

/-- The first generated pair may be the first adversary query.  In that case
the replay pauses at program start with zero consumed prefix queries; the
restored verifier state remains the explicit complete nonempty dummy state. -/
theorem construct_atomic_pair_replay_success_allows_empty_q1_prefix
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (output :
      {run : AtomicPairReplayOutput TapeIdentity Statement Proof Result //
        IsOperationalAtomicPairReplay source.origin execution generated configuration
          run})
    (success : constructAtomicPairReplay source execution generated
      configuration = .ok output)
    (emptyBefore : output.1.occurrence.before = []) :
    output.1.prefixRun.steps = 0 ∧
      NonemptyVerifierHistory
        (concreteRestoration execution generated).sourceExecution.interactiveState := by
  have operational := output.2
  rcases operational with
    ⟨tape, identity, q1, occurrenceFound, split, beforeFresh, chosenInput,
      actor, pendingChosen, halfClassification, pendingHalf, assigned,
      prefixDefinition, paused, residual, trace, freshOutput, freshAdvance,
      distinct, programmingOrder, programmed, replayDefinition, pendingQuery,
      returned, initialHistory, replayHistory, prefixSteps, replaySteps,
      replayFuelBound, resources, withinBudget⟩
  exact ⟨by simpa [emptyBefore] using prefixSteps,
    restoration_first_run_history_is_nonempty
      (concreteRestoration execution generated)⟩

#print axioms half_for_output_input
#print axioms half_for_advance_input
#print axioms half_for_pair_input_some_is_exact
#print axioms atomic_pair_resource_increments_exact
#print axioms program_oracle_success_exact
#print axioms program_oracle_success_preserves_lookup_answer
#print axioms program_pair_in_order_success_exact
#print axioms program_atomic_pair_success_exact
#print axioms run_prefix_paused_steps_eq_fuel
#print axioms run_machine_returned_query_has_positive_steps
#print axioms query_oracle_success_preserves_programming_history
#print axioms run_machine_preserves_programming_history
#print axioms atomic_run_machine_steps_le_fuel
#print axioms run_machine_returned_query_exposes_first_call
#print axioms query_oracle_success_uses_cached_lookup_answer
#print axioms constructAtomicPairReplay
#print axioms construct_atomic_pair_replay_success_is_operational
#print axioms construct_atomic_pair_replay_success_preserves_origin_and_q1
#print axioms construct_atomic_pair_replay_success_has_exact_prefix_and_resources
#print axioms construct_atomic_pair_replay_success_programs_both_and_resumes_assigned
#print axioms construct_atomic_pair_replay_success_has_exact_resource_increments
#print axioms construct_atomic_pair_replay_success_relates_complete_restoration
#print axioms construct_atomic_pair_replay_success_allows_empty_q1_prefix

end AspisK1.V7Tag73AtomicPairReplay
