import Mathlib.Probability.Distributions.Uniform
import AspisFormal.K1.V7FsAokExperiment

/-!
# Finite classical-ROM state-restoration coupling core

This file supplies a start-only, same-randomness replay construction.  The
extractor receives a closure over the fixed tape, never the tape itself, and
the black box is never handed an opaque internal adversary checkpoint. Instead,
the construction starts the closed adversary, replays a
concrete nonempty prefix of the frozen first-run query/answer record, pauses at
the next transcript-driving query, programs that still-undefined point, and
continues the residual oracle program.

The construction is an algorithm returning `Except CouplingFailure`; its
`Option` projection is the requested deterministic partial map.  Successful
outputs are checked against an operational predicate containing only tape,
query-history, derived-checkpoint, and resource-accounting invariants.  No
Fiat--Shamir security inequality, BCS theorem, trace-cover statement, or
extraction conclusion is a field or premise.

The finite counting section proves exact facts for a uniform element of the
full `2^256` output space, including fixed-target, finite-target, union, and
quadratic accounting.  The remaining adaptive lazy-oracle instantiation is
named only as a proposition definition at the end.
-/

set_option autoImplicit false

namespace AspisK1.V7FsStateRestorationCoupling

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment

/-! ## Start-only same-tape replay -/

/-- A classical black box that can only be started from its computation
start.  There is deliberately no `resume` operation at an arbitrary opaque
adversary checkpoint. -/
structure SameTapeBlackBox
    (HiddenTape Observation Result : Type*) where
  start : HiddenTape → Observation → OracleMachine Result

/-- The extractor-visible start capability.  `TapeIdentity` is an opaque
public identity token; the hidden tape is captured only in the closure. -/
structure SameTapeStartCapability
    (TapeIdentity Observation Result : Type*) where
  tapeIdentity : TapeIdentity
  start : Observation → OracleMachine Result

def closeSameTapeStart
    {HiddenTape TapeIdentity Observation Result : Type*}
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity) :
    SameTapeStartCapability TapeIdentity Observation Result where
  tapeIdentity := identity
  start observation := blackBox.start hiddenTape observation

@[simp] theorem closeSameTapeStart_identity
    {HiddenTape TapeIdentity Observation Result : Type*}
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity) :
    (closeSameTapeStart blackBox hiddenTape identity).tapeIdentity = identity := by
  rfl

@[simp] theorem closeSameTapeStart_program
    {HiddenTape TapeIdentity Observation Result : Type*}
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity)
    (observation : Observation) :
    (closeSameTapeStart blackBox hiddenTape identity).start observation =
      blackBox.start hiddenTape observation := by
  rfl

/-! ### Experiment origin for the hidden-tape closure -/

/-- Public data emitted when the experiment performs the original adversary
run and creates its restart capability.  Notice that `HiddenTape` is not a
parameter of this type and there is no tape projection: the tape occurs only
inside `capability.start`.

The construction below, rather than a field of this structure, establishes
that `firstExecution` and `capability` came from the same closed start
program. -/
structure SameTapeExperimentOrigin
    (TapeIdentity Observation Statement Proof Result : Type*) where
  observation : Observation
  initialOracle : OracleState
  firstExecution : MachineRun Result
  firstRun : FirstRun TapeIdentity Statement Proof
  capability : SameTapeStartCapability TapeIdentity Observation Result

/-- Extract a public proof only from a normally returned first execution.
Oracle aborts and timeouts do not manufacture a forgery. -/
def returnedForgery
    {Statement Proof Result : Type*}
    (forgeryOf : Result → Option (PublicProof Statement Proof)) :
    MachineHalt Result → Option (PublicProof Statement Proof)
  | .returned result => forgeryOf result
  | .oracleAbort _ => none
  | .outOfFuel => none

/-- Run the original adversary and close the restart entry point over exactly
the same hidden tape.  The experiment's opaque `identity` token is copied into
both public records, but `hiddenTape` is not retained as an
extractor-visible field.  As elsewhere in this development, opacity of the
token is a modeling convention: this constructor neither derives it from nor
claims that it cryptographically hides the tape.

This is an experiment-side constructor.  In particular, the coupling
algorithm still consumes only the resulting `SameTapeStartCapability`; it is
never given `hiddenTape`. -/
def makeSameTapeExperimentOrigin
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity)
    (observation : Observation) (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat) (initialOracle : OracleState)
    (forgeryOf : Result → Option (PublicProof Statement Proof)) :
    SameTapeExperimentOrigin TapeIdentity Observation Statement Proof Result :=
  let capability := closeSameTapeStart blackBox hiddenTape identity
  let execution := runMachine controller limits .adversary fuel initialOracle
    (capability.start observation)
  { observation := observation
    initialOracle := initialOracle
    firstExecution := execution
    firstRun :=
      { tapeIdentity := identity
        forgery := returnedForgery forgeryOf execution.halt
        stateAtAdversaryHalt := execution.oracle }
    capability := capability }

/-- The public first-run identity and the restart-capability identity are the
same token because the experiment creates both in one hidden-tape closure. -/
@[simp] theorem makeSameTapeExperimentOrigin_identity
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity)
    (observation : Observation) (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat) (initialOracle : OracleState)
    (forgeryOf : Result → Option (PublicProof Statement Proof)) :
    (makeSameTapeExperimentOrigin blackBox hiddenTape identity observation
      controller limits fuel initialOracle forgeryOf).firstRun.tapeIdentity =
    (makeSameTapeExperimentOrigin blackBox hiddenTape identity observation
      controller limits fuel initialOracle forgeryOf).capability.tapeIdentity := by
  rfl

/-- The first execution is literally obtained by starting the opaque
capability, not by resuming an adversary checkpoint. -/
theorem makeSameTapeExperimentOrigin_first_execution
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity)
    (observation : Observation) (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat) (initialOracle : OracleState)
    (forgeryOf : Result → Option (PublicProof Statement Proof)) :
    (makeSameTapeExperimentOrigin blackBox hiddenTape identity observation
      controller limits fuel initialOracle forgeryOf).firstExecution =
      runMachine controller limits .adversary fuel initialOracle
        ((makeSameTapeExperimentOrigin blackBox hiddenTape identity observation
          controller limits fuel initialOracle forgeryOf).capability.start
            observation) := by
  rfl

/-- The capability's start program is the original black-box start with the
same hidden tape captured by the experiment.  The returned origin object has
no operation that reveals that tape. -/
theorem makeSameTapeExperimentOrigin_same_hidden_tape_start
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity)
    (observation : Observation) (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat) (initialOracle : OracleState)
    (forgeryOf : Result → Option (PublicProof Statement Proof)) :
    (makeSameTapeExperimentOrigin blackBox hiddenTape identity observation
      controller limits fuel initialOracle forgeryOf).capability.start observation =
      blackBox.start hiddenTape observation := by
  rfl

/-- The oracle state frozen into `FirstRun` is exactly the state at the end of
the experiment's first execution. -/
@[simp] theorem makeSameTapeExperimentOrigin_first_run_state
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity)
    (observation : Observation) (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat) (initialOracle : OracleState)
    (forgeryOf : Result → Option (PublicProof Statement Proof)) :
    (makeSameTapeExperimentOrigin blackBox hiddenTape identity observation
      controller limits fuel initialOracle forgeryOf).firstRun.stateAtAdversaryHalt =
    (makeSameTapeExperimentOrigin blackBox hiddenTape identity observation
      controller limits fuel initialOracle forgeryOf).firstExecution.oracle := by
  rfl

/-- The public origin retains the exact oracle state from which its first
execution was started. -/
@[simp] theorem makeSameTapeExperimentOrigin_initialOracle
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (blackBox : SameTapeBlackBox HiddenTape Observation Result)
    (hiddenTape : HiddenTape) (identity : TapeIdentity)
    (observation : Observation) (controller : AdaptiveController)
    (limits : OracleLimits) (fuel : Nat) (initialOracle : OracleState)
    (forgeryOf : Result → Option (PublicProof Statement Proof)) :
    (makeSameTapeExperimentOrigin blackBox hiddenTape identity observation
      controller limits fuel initialOracle forgeryOf).initialOracle =
      initialOracle := by
  rfl

/-- The first occurrence of a transcript-driving query, with its concrete
prefix and suffix.  This is produced by `splitAtDrivingQuery`, not supplied as
an existential certificate. -/
structure DrivingSplit (history : List QueryRecord) (input : ShaInput) where
  before : List QueryRecord
  driving : QueryRecord
  after : List QueryRecord
  decomposition : history = before ++ driving :: after
  drivingInput : driving.input = input

def splitAtDrivingQuery (input : ShaInput) :
    (history : List QueryRecord) → Option (DrivingSplit history input)
  | [] => none
  | record :: rest =>
      if inputMatches : record.input = input then
        some
          { before := []
            driving := record
            after := rest
            decomposition := rfl
            drivingInput := inputMatches }
      else
        match splitAtDrivingQuery input rest with
        | none => none
        | some split =>
            some
              { before := record :: split.before
                driving := split.driving
                after := split.after
                decomposition := by simp [split.decomposition]
                drivingInput := split.drivingInput }

theorem splitAtDrivingQuery_success
    (input : ShaInput) (history : List QueryRecord)
    (split : DrivingSplit history input)
    (success : splitAtDrivingQuery input history = some split) :
    history = split.before ++ split.driving :: split.after ∧
      split.driving.input = input := by
  exact ⟨split.decomposition, split.drivingInput⟩

/-- A prefix interpreter retaining the residual program at fuel exhaustion.
Unlike an arbitrary state-restoration interface, this checkpoint can only be
obtained by executing `program` from its start. -/
inductive PrefixHalt (Result : Type*) where
  | paused (residual : OracleMachine Result)
  | returned (result : Result)
  | oracleAbort (reason : OracleAbort)

structure PrefixRun (Result : Type*) where
  halt : PrefixHalt Result
  oracle : OracleState
  steps : Nat

def runPrefix {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) : Nat → OracleState → OracleMachine Result →
      PrefixRun Result
  | 0, state, program =>
      { halt := .paused program, oracle := state, steps := 0 }
  | _, state, .pure result =>
      { halt := .returned result, oracle := state, steps := 0 }
  | _, state, .abort reason =>
      { halt := .oracleAbort reason, oracle := state, steps := 0 }
  | fuel + 1, state, .query input next =>
      match queryOracle controller limits actor state input with
      | .error reason =>
          { halt := .oracleAbort reason, oracle := state, steps := 1 }
      | .ok (output, nextState) =>
          let result := runPrefix controller limits actor fuel nextState
            (next output)
          { result with steps := result.steps + 1 }

def queryAnswerTrace (history : List QueryRecord) :
    List (ShaInput × ShaOutput) :=
  history.map fun record => (record.input, record.output)

def historySince (initial final : OracleState) : List QueryRecord :=
  final.history.drop initial.history.length

/-- Replay the first-run answers in order.  The controller indexes from the
initial history length so prior simulator/verifier records cannot be mistaken
for adversary-prefix answers. -/
def recordedPrefixController (initialHistoryLength : Nat)
    (recorded : List QueryRecord) : AdaptiveController :=
  fun history input =>
    match recorded[history.length - initialHistoryLength]? with
    | none => .refuse
    | some expected =>
        if expected.input = input then .answer expected.output else .refuse

structure FixedFirstRunRecord
    (RandomTape Observation Statement Proof Result : Type*) where
  observation : Observation
  firstRun : FirstRun RandomTape Statement Proof
  /-- Shared oracle state before the start-only adversary computation.  It may
  contain canonical-simulator programming, but the map never treats it as an
  adversary checkpoint. -/
  initialOracle : OracleState
  firstRunUse : ResourceUse
  transcriptDrivingInput : ShaInput
  forkOutput : ShaOutput
  postForkController : AdaptiveController
  oracleLimits : OracleLimits
  budget : ResourceBudget
  replayFuel : Nat

/-! ### Restricting replay inputs to one experiment origin -/

/-- Replay controls and resource accounting that are not part of the hidden
tape origin.  In particular, this structure cannot replace the origin's
observation, first run, or start capability. -/
structure OriginReplayConfiguration where
  /-- This value remains configurable because `SameTapeExperimentOrigin`
  records execution state, not the surrounding experiment's resource ledger.
  A caller using this in a compiler theorem must separately prove equality to
  the actual first-run resource accounting. -/
  firstRunUse : ResourceUse
  transcriptDrivingInput : ShaInput
  forkOutput : ShaOutput
  postForkController : AdaptiveController
  oracleLimits : OracleLimits
  budget : ResourceBudget
  replayFuel : Nat

/-- Build the generic replay record while sourcing its observation, initial
oracle, and frozen first run exclusively from the same experiment origin. -/
def fixedFirstRunRecordFromOrigin
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    FixedFirstRunRecord TapeIdentity Observation Statement Proof Result where
  observation := origin.observation
  firstRun := origin.firstRun
  initialOracle := origin.initialOracle
  firstRunUse := configuration.firstRunUse
  transcriptDrivingInput := configuration.transcriptDrivingInput
  forkOutput := configuration.forkOutput
  postForkController := configuration.postForkController
  oracleLimits := configuration.oracleLimits
  budget := configuration.budget
  replayFuel := configuration.replayFuel

@[simp] theorem fixedFirstRunRecordFromOrigin_observation
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).observation =
      origin.observation := by
  rfl

@[simp] theorem fixedFirstRunRecordFromOrigin_firstRun
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).firstRun =
      origin.firstRun := by
  rfl

@[simp] theorem fixedFirstRunRecordFromOrigin_initialOracle
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).initialOracle =
      origin.initialOracle := by
  rfl

@[simp] theorem fixedFirstRunRecordFromOrigin_firstRunUse
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).firstRunUse =
      configuration.firstRunUse := by
  rfl

@[simp] theorem fixedFirstRunRecordFromOrigin_transcriptDrivingInput
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).transcriptDrivingInput =
      configuration.transcriptDrivingInput := by
  rfl

@[simp] theorem fixedFirstRunRecordFromOrigin_forkOutput
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).forkOutput =
      configuration.forkOutput := by
  rfl

@[simp] theorem fixedFirstRunRecordFromOrigin_postForkController
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).postForkController =
      configuration.postForkController := by
  rfl

@[simp] theorem fixedFirstRunRecordFromOrigin_oracleLimits
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).oracleLimits =
      configuration.oracleLimits := by
  rfl

@[simp] theorem fixedFirstRunRecordFromOrigin_budget
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).budget =
      configuration.budget := by
  rfl

@[simp] theorem fixedFirstRunRecordFromOrigin_replayFuel
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    (fixedFirstRunRecordFromOrigin origin configuration).replayFuel =
      configuration.replayFuel := by
  rfl

inductive PrefixFailure where
  | missingTranscriptDrivingQuery
  /-- This rejects a vacuous start replay.  It is not, by itself, the BCS
  restriction to a non-null previously-seen complete verifier state. -/
  | emptyReplayPrefix
  | replayEndedBeforeDerivedPause
  | replayDidNotReachDrivingQuery
  | recordedPrefixMismatch
  deriving DecidableEq, Repr

inductive ProgrammingFailure where
  | tableOrProgrammingCollision
  | programmingBudget
  | unexpectedOracleAbort (reason : OracleAbort)
  deriving DecidableEq, Repr

inductive BudgetFailure where
  | totalOracleCalls
  | freshOracleAnswers
  | postForkControllerRefused
  | finalResourceBudget
  deriving DecidableEq, Repr

inductive ExecutionFailure where
  | timeout
  | machineAbort (reason : OracleAbort)
  | emptyOperationalReplay
  deriving DecidableEq, Repr

inductive CouplingFailure where
  | prefix (reason : PrefixFailure)
  | programming (reason : ProgrammingFailure)
  | budget (reason : BudgetFailure)
  | execution (reason : ExecutionFailure)
  | operationalInvariantCheck
  deriving DecidableEq, Repr

def classifyOracleAbort : OracleAbort → CouplingFailure
  | .totalCallBudget => .budget .totalOracleCalls
  | .freshCallBudget => .budget .freshOracleAnswers
  | .programmingBudget => .programming .programmingBudget
  | .programmingConflict => .programming .tableOrProgrammingCollision
  | .controllerRefused => .budget .postForkControllerRefused

def couplingResourceUse (firstRunUse : ResourceUse)
    (prefixSteps replaySteps : Nat) (finalOracle : OracleState) : ResourceUse :=
  { firstRunUse with
    extractorOracleCalls :=
      firstRunUse.extractorOracleCalls + prefixSteps + replaySteps
    freshOracleAnswers := finalOracle.freshCalls
    programmedPoints := finalOracle.programmingHistory.length
    restartCount := firstRunUse.restartCount + 1
    runtimeSteps := firstRunUse.runtimeSteps + prefixSteps + replaySteps }

/-- Operational output of the deterministic construction.  `checkpoint*`
fields are derived by start-only replay; no checkpoint is an input. -/
structure CoupledReplay
    (RandomTape Statement Proof Result : Type*) where
  tapeIdentity : RandomTape
  q1 : List QueryRecord
  replayPrefix : List QueryRecord
  driving : QueryRecord
  suffix : List QueryRecord
  prefixRun : PrefixRun Result
  derivedPausePrefixLength : Nat
  derivedPauseOracle : OracleState
  residualProgram : OracleMachine Result
  programmedOutput : ShaOutput
  replayRun : MachineRun Result
  returned : Result
  newReplayQueries : List QueryRecord
  resources : ResourceUse

/-- Purely operational legality: exact fixed tape identity and Q1, a nonempty
prefix reconstructed from start, the inherited histories, one real post-fork
oracle query, and exact resource accounting.  The derived pause is an
adversary-program pause, not yet a complete interactive-verifier state. -/
def IsOperationalCoupling
    {RandomTape Observation Statement Proof Result : Type*}
    (capability : SameTapeStartCapability RandomTape Observation Result)
    (record : FixedFirstRunRecord
      RandomTape Observation Statement Proof Result)
    (output : CoupledReplay RandomTape Statement Proof Result) : Prop :=
  output.tapeIdentity = capability.tapeIdentity ∧
  capability.tapeIdentity = record.firstRun.tapeIdentity ∧
  output.q1 = record.firstRun.q1 ∧
  output.q1 = output.replayPrefix ++ output.driving :: output.suffix ∧
  output.driving.input = record.transcriptDrivingInput ∧
  0 < output.replayPrefix.length ∧
  output.derivedPausePrefixLength = output.replayPrefix.length ∧
  output.derivedPauseOracle = output.prefixRun.oracle ∧
  output.prefixRun.halt = .paused output.residualProgram ∧
  queryAnswerTrace (historySince record.initialOracle output.prefixRun.oracle) =
    queryAnswerTrace output.replayPrefix ∧
  record.initialOracle.history <+: output.prefixRun.oracle.history ∧
  output.prefixRun.oracle.history <+: output.replayRun.oracle.history ∧
  output.replayRun.halt = .returned output.returned ∧
  output.newReplayQueries =
    output.replayRun.oracle.history.drop output.prefixRun.oracle.history.length ∧
  0 < output.newReplayQueries.length ∧
  output.resources = couplingResourceUse record.firstRunUse
    output.prefixRun.steps output.replayRun.steps output.replayRun.oracle ∧
  output.resources.adversaryOracleCalls = record.firstRun.q1.length ∧
  WithinBudget output.resources record.budget

private noncomputable def constructCandidate
    {RandomTape Observation Statement Proof Result : Type*}
    (capability : SameTapeStartCapability RandomTape Observation Result)
    (record : FixedFirstRunRecord
      RandomTape Observation Statement Proof Result) :
    Except CouplingFailure (CoupledReplay RandomTape Statement Proof Result) := by
  classical
  exact match splitAtDrivingQuery record.transcriptDrivingInput record.firstRun.q1 with
  | none => .error (.prefix .missingTranscriptDrivingQuery)
  | some split =>
      if split.before.isEmpty then
        .error (.prefix .emptyReplayPrefix)
      else
        let prefixRun := runPrefix
          (recordedPrefixController record.initialOracle.history.length
            split.before)
          record.oracleLimits .extractorReplay split.before.length
          record.initialOracle
          (capability.start record.observation)
        match prefixRun.halt with
        | .returned _ =>
            .error (.prefix .replayEndedBeforeDerivedPause)
        | .oracleAbort reason => .error (classifyOracleAbort reason)
        | .paused residual =>
            match residual with
            | .pure _ | .abort _ =>
                .error (.prefix .replayEndedBeforeDerivedPause)
            | .query pendingInput next =>
                if pendingInput ≠ split.driving.input then
                  .error (.prefix .replayDidNotReachDrivingQuery)
                else if queryAnswerTrace
                    (historySince record.initialOracle prefixRun.oracle) ≠
                    queryAnswerTrace split.before then
                  .error (.prefix .recordedPrefixMismatch)
                else
                  let programming : Programming :=
                    { input := pendingInput, output := record.forkOutput }
                  match programOracle record.oracleLimits .extractorReplay
                      prefixRun.oracle programming with
                  | .error reason => .error (classifyOracleAbort reason)
                  | .ok programmedOracle =>
                      if record.replayFuel = 0 then
                        .error (.execution .timeout)
                      else
                        let replayRun := runMachine record.postForkController
                          record.oracleLimits .extractorReplay record.replayFuel
                          programmedOracle (.query pendingInput next)
                        match replayRun.halt with
                        | .outOfFuel => .error (.execution .timeout)
                        | .oracleAbort reason =>
                            .error (classifyOracleAbort reason)
                        | .returned result =>
                            let newQueries := replayRun.oracle.history.drop
                              prefixRun.oracle.history.length
                            if newQueries.isEmpty then
                              .error (.execution .emptyOperationalReplay)
                            else
                              let resources := couplingResourceUse
                                record.firstRunUse prefixRun.steps
                                  replayRun.steps replayRun.oracle
                              if resources.adversaryOracleCalls ≠
                                  record.firstRun.q1.length then
                                .error .operationalInvariantCheck
                              else if _withinBudget :
                                  WithinBudget resources record.budget then
                                .ok
                                  { tapeIdentity := capability.tapeIdentity
                                    q1 := record.firstRun.q1
                                    replayPrefix := split.before
                                    driving := split.driving
                                    suffix := split.after
                                    prefixRun := prefixRun
                                    derivedPausePrefixLength := split.before.length
                                    derivedPauseOracle := prefixRun.oracle
                                    residualProgram := residual
                                    programmedOutput := record.forkOutput
                                    replayRun := replayRun
                                    returned := result
                                    newReplayQueries := newQueries
                                    resources := resources }
                              else
                                .error (.budget .finalResourceBudget)

private theorem queryOracle_success_history_prefix
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    state.history <+: nextState.history := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact List.prefix_append _ _
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next _ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          exact List.prefix_append _ _

private theorem runPrefix_history_prefix
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    state.history <+: (runPrefix controller limits actor fuel state program).oracle.history := by
  induction fuel generalizing state program with
  | zero => simp [runPrefix]
  | succ fuel inductionHypothesis =>
      cases program with
      | pure result => simp [runPrefix]
      | abort reason => simp [runPrefix]
      | query input next =>
          simp only [runPrefix]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simp
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              exact (queryOracle_success_history_prefix controller limits actor
                state nextState input output queryResult).trans
                  (inductionHypothesis nextState (next output))

private theorem runMachine_history_prefix
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    state.history <+: (runMachine controller limits actor fuel state program).oracle.history := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> simp [runMachine]
  | succ fuel inductionHypothesis =>
      cases program with
      | pure result => simp [runMachine]
      | abort reason => simp [runMachine]
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simp
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              exact (queryOracle_success_history_prefix controller limits actor
                state nextState input output queryResult).trans
                  (inductionHypothesis nextState (next output))

/-- Detailed deterministic map with explicit failure reasons.  The final
operational check is decidable and contains no cryptographic conclusion. -/
noncomputable def constructLegalReplay
    {RandomTape Observation Statement Proof Result : Type*}
    (capability : SameTapeStartCapability RandomTape Observation Result)
    (record : FixedFirstRunRecord
      RandomTape Observation Statement Proof Result) :
    Except CouplingFailure
      {output : CoupledReplay RandomTape Statement Proof Result //
        IsOperationalCoupling capability record output} := by
  classical
  match candidateResult : constructCandidate capability record with
  | .error reason => exact .error reason
  | .ok output =>
      if operational : IsOperationalCoupling capability record output then
        exact .ok ⟨output, operational⟩
      else
        exact .error .operationalInvariantCheck

/-- Requested deterministic partial map. -/
noncomputable def constructLegalReplay?
    {RandomTape Observation Statement Proof Result : Type*}
    (capability : SameTapeStartCapability RandomTape Observation Result)
    (record : FixedFirstRunRecord
      RandomTape Observation Statement Proof Result) :
    Option {output : CoupledReplay RandomTape Statement Proof Result //
      IsOperationalCoupling capability record output} :=
  (constructLegalReplay capability record).toOption

/-- Origin-restricted entry point.  Callers supply only one experiment origin
and replay controls; the capability, observation, and frozen first run cannot
be mixed across origins. -/
noncomputable def constructLegalReplayFromOrigin?
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    Option
      {output : CoupledReplay TapeIdentity Statement Proof Result //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin configuration) output} :=
  constructLegalReplay? origin.capability
    (fixedFirstRunRecordFromOrigin origin configuration)

@[simp] theorem constructLegalReplayFromOrigin_unfold
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration) :
    constructLegalReplayFromOrigin? origin configuration =
      constructLegalReplay? origin.capability
        (fixedFirstRunRecordFromOrigin origin configuration) := by
  rfl

theorem map_success_is_operational
    {RandomTape Observation Statement Proof Result : Type*}
    (capability : SameTapeStartCapability RandomTape Observation Result)
    (record : FixedFirstRunRecord
      RandomTape Observation Statement Proof Result)
    (output : {run : CoupledReplay RandomTape Statement Proof Result //
      IsOperationalCoupling capability record run})
    (success : constructLegalReplay? capability record = some output) :
    IsOperationalCoupling capability record output.1 := by
  exact output.2

theorem map_success_preserves_identity_q1_pause_history_resources
    {RandomTape Observation Statement Proof Result : Type*}
    (capability : SameTapeStartCapability RandomTape Observation Result)
    (record : FixedFirstRunRecord
      RandomTape Observation Statement Proof Result)
    (output : {run : CoupledReplay RandomTape Statement Proof Result //
      IsOperationalCoupling capability record run})
    (success : constructLegalReplay? capability record = some output) :
    capability.tapeIdentity = record.firstRun.tapeIdentity ∧
    output.1.tapeIdentity = record.firstRun.tapeIdentity ∧
    output.1.q1 = record.firstRun.q1 ∧
    0 < output.1.derivedPausePrefixLength ∧
    record.initialOracle.history <+: output.1.prefixRun.oracle.history ∧
    output.1.prefixRun.oracle.history <+: output.1.replayRun.oracle.history ∧
    0 < output.1.newReplayQueries.length ∧
    output.1.resources = couplingResourceUse record.firstRunUse
      output.1.prefixRun.steps output.1.replayRun.steps
        output.1.replayRun.oracle ∧
    WithinBudget output.1.resources record.budget := by
  have legal := map_success_is_operational capability record output success
  rcases legal with
    ⟨outputIdentity, capabilityIdentity, q1, decomposition, driving, prefixNonempty,
      checkpointLength, checkpointOracle, checkpointProgram,
      trace, initialHistory, replayHistory, returned, newQueries,
      replayNonempty, resources, adversaryCalls, withinBudget⟩
  exact ⟨capabilityIdentity, outputIdentity.trans capabilityIdentity, q1,
    checkpointLength.symm ▸ prefixNonempty,
    initialHistory, replayHistory, replayNonempty, resources, withinBudget⟩

/-- A successful origin-restricted replay exposes the same operational facts
as the generic map, now stated directly against the single supplied origin.
This still does not assert complete-verifier-state restoration, acceptance,
or extraction. -/
theorem map_from_origin_success_preserves_identity_q1_pause_history_resources
    {TapeIdentity Observation Statement Proof Result : Type*}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (configuration : OriginReplayConfiguration)
    (output :
      {run : CoupledReplay TapeIdentity Statement Proof Result //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin configuration) run})
    (success : constructLegalReplayFromOrigin? origin configuration =
      some output) :
    origin.capability.tapeIdentity = origin.firstRun.tapeIdentity ∧
    output.1.tapeIdentity = origin.firstRun.tapeIdentity ∧
    output.1.q1 = origin.firstRun.q1 ∧
    0 < output.1.derivedPausePrefixLength ∧
    origin.initialOracle.history <+:
      output.1.prefixRun.oracle.history ∧
    output.1.prefixRun.oracle.history <+:
      output.1.replayRun.oracle.history ∧
    0 < output.1.newReplayQueries.length ∧
    output.1.resources = couplingResourceUse configuration.firstRunUse
      output.1.prefixRun.steps output.1.replayRun.steps
        output.1.replayRun.oracle ∧
    WithinBudget output.1.resources configuration.budget := by
  have genericSuccess :
      constructLegalReplay? origin.capability
        (fixedFirstRunRecordFromOrigin origin configuration) = some output := by
    simpa only [constructLegalReplayFromOrigin_unfold] using success
  simpa using
    (map_success_preserves_identity_q1_pause_history_resources
      origin.capability (fixedFirstRunRecordFromOrigin origin configuration)
      output genericSuccess)

theorem prefix_run_history_is_preserved
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    state.history <+:
      (runPrefix controller limits actor fuel state program).oracle.history :=
  runPrefix_history_prefix controller limits actor fuel state program

theorem postfork_run_history_is_preserved
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    state.history <+:
      (runMachine controller limits actor fuel state program).oracle.history :=
  runMachine_history_prefix controller limits actor fuel state program

/-! ## Explicitly missing verifier-state refinement -/

/-- Smallest deterministic refinement still required before the pauses above
can be called legal *restricted state-restoration verifier states*.  The exact
Tag-73 query DAG must reconstruct a non-null, complete, previously seen
verifier state.  This proposition is only a definition: it is not a field of
the coupling map and no theorem in this file assumes it. -/
def Tag73QueryDagToCompleteVerifierStateMapNeeded
    {QueryNode VerifierState : Type*}
    (queryDag : List QueryNode)
    (restore : List QueryNode → Option VerifierState)
    (isCompletePreviouslySeen : List QueryNode → VerifierState → Prop) : Prop :=
  ∀ replayPrefix,
    replayPrefix ≠ [] → replayPrefix <+: queryDag →
      ∃ state, restore replayPrefix = some state ∧
        isCompletePreviouslySeen replayPrefix state

/-! ## Exact finite-uniform 256-bit accounting -/

/-- A mathematically exact encoding of the SHA-256 output space. -/
abbrev FullOutput256 := Fin (2 ^ 256)

/-! ### The deployed 32-byte digest really has `2^256` values -/

/-- The concrete core conversion between one deployed byte and its 256
possible values.  This uses `UInt8.toFin`/`UInt8.ofFin` and their inverse
lemmas; no choice is involved. -/
def uint8EquivFin256 : UInt8 ≃ Fin 256 :=
  ({ toFun := UInt8.toFin
     invFun := UInt8.ofFin
     left_inv := UInt8.ofFin_toFin
     right_inv := UInt8.toFin_ofFin } : UInt8 ≃ Fin UInt8.size).trans
    (finCongr (by decide : UInt8.size = 256))

/-- Apply the concrete byte conversion independently at each of the 32
deployed digest positions. -/
def digest256EquivFinByteVector :
    Digest256 ≃ (Fin 32 → Fin 256) :=
  Equiv.arrowCongr (Equiv.refl (Fin 32)) uint8EquivFin256

@[simp] theorem digest256EquivFinByteVector_apply
    (digest : Digest256) (index : Fin 32) :
    digest256EquivFinByteVector digest index =
      uint8EquivFin256 (digest index) := by
  rfl

theorem fin_byte_vector_256_cardinality :
    Fintype.card (Fin 32 → Fin 256) = 2 ^ 256 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  calc
    256 ^ 32 = (2 ^ 8) ^ 32 := by norm_num
    _ = 2 ^ (8 * 32) := by rw [pow_mul]
    _ = 2 ^ 256 := by norm_num

/-- Cardinality of the exact deployed representation
`Digest256 = Fin 32 → UInt8`. -/
theorem deployed_digest_256_cardinality :
    Fintype.card Digest256 = 2 ^ 256 := by
  calc
    Fintype.card Digest256 = Fintype.card (Fin 32 → Fin 256) :=
      Fintype.card_congr digest256EquivFinByteVector
    _ = 2 ^ 256 := fin_byte_vector_256_cardinality

/-- Cardinality-first enumeration of 32 finite bytes by one element of
`Fin (2^256)`.  The bytewise part is the concrete conversion above.  The last
step uses `Fintype.equivFinOfCardEq`, so this definition intentionally makes
no claim about the deployed serialization's endian convention; K1.6 needs
only a bijection and uniform-law transport. -/
noncomputable def finByteVectorCardinalityEquivFullOutput256 :
    (Fin 32 → Fin 256) ≃ FullOutput256 :=
  Fintype.equivFinOfCardEq fin_byte_vector_256_cardinality

/-- A genuine bijection from the deployed digest type to the exact full
256-bit output space. -/
noncomputable def digest256EquivFullOutput256 :
    Digest256 ≃ FullOutput256 :=
  digest256EquivFinByteVector.trans
    finByteVectorCardinalityEquivFullOutput256

noncomputable def uniformFullOutput256 : PMF FullOutput256 :=
  PMF.uniformOfFintype FullOutput256

/-- The exact full-output uniform law transported back to deployed digests
along `digest256EquivFullOutput256`. -/
noncomputable def transportedUniformDigest256 : PMF Digest256 :=
  uniformFullOutput256.map digest256EquivFullOutput256.symm

/-- The directly defined uniform law on the deployed digest representation. -/
noncomputable def uniformDigest256 : PMF Digest256 :=
  PMF.uniformOfFintype Digest256

theorem full_output_256_cardinality :
    Fintype.card FullOutput256 = 2 ^ 256 := by
  exact Fintype.card_fin _

theorem uniform_full_output_point_mass (output : FullOutput256) :
    uniformFullOutput256 output = ((2 : ENNReal) ^ 256)⁻¹ := by
  unfold uniformFullOutput256
  rw [PMF.uniformOfFintype_apply]
  congr 1
  norm_num [FullOutput256]

theorem uniform_full_output_guess_probability (guess : FullOutput256) :
    uniformFullOutput256.toOuterMeasure ({guess} : Set FullOutput256) =
      1 / ((2 : ENNReal) ^ 256) := by
  rw [PMF.toOuterMeasure_apply_singleton,
    uniform_full_output_point_mass, one_div]

/-- Transporting full-output uniformity through the digest bijection gives
exactly `2^-256` mass to every deployed digest singleton. -/
theorem transported_uniform_digest_singleton_probability
    (digest : Digest256) :
    transportedUniformDigest256.toOuterMeasure
        ({digest} : Set Digest256) =
      1 / ((2 : ENNReal) ^ 256) := by
  unfold transportedUniformDigest256
  rw [PMF.toOuterMeasure_map_apply]
  have preimage_singleton :
      digest256EquivFullOutput256.symm ⁻¹' ({digest} : Set Digest256) =
        ({digest256EquivFullOutput256 digest} : Set FullOutput256) := by
    ext output
    change (digest256EquivFullOutput256.symm output = digest) ↔
      (output = digest256EquivFullOutput256 digest)
    constructor
    · intro equality
      simpa using congrArg digest256EquivFullOutput256 equality
    · intro equality
      simpa using congrArg digest256EquivFullOutput256.symm equality
  rw [preimage_singleton]
  exact uniform_full_output_guess_probability _

theorem transported_uniform_digest_point_mass (digest : Digest256) :
    transportedUniformDigest256 digest =
      ((2 : ENNReal) ^ 256)⁻¹ := by
  rw [← PMF.toOuterMeasure_apply_singleton,
    transported_uniform_digest_singleton_probability, one_div]

theorem uniform_digest_point_mass (digest : Digest256) :
    uniformDigest256 digest = ((2 : ENNReal) ^ 256)⁻¹ := by
  unfold uniformDigest256
  rw [PMF.uniformOfFintype_apply, deployed_digest_256_cardinality]
  norm_num

/-- Uniformity is representation-independent: transporting the exact
`Fin (2^256)` law through the bijection is the same PMF as uniform sampling
directly from the deployed 32-byte digest type. -/
theorem transported_uniform_digest_eq_uniform :
    transportedUniformDigest256 = uniformDigest256 := by
  ext digest : 1
  rw [transported_uniform_digest_point_mass,
    uniform_digest_point_mass]

def finiteTargets {count : Nat} (targets : Fin count → FullOutput256) :
    Finset FullOutput256 :=
  Finset.univ.image targets

theorem finiteTargets_card_le {count : Nat}
    (targets : Fin count → FullOutput256) :
    (finiteTargets targets).card ≤ count := by
  calc
    (finiteTargets targets).card ≤ (Finset.univ : Finset (Fin count)).card :=
      Finset.card_image_le
    _ = count := by simp

theorem uniform_full_output_hits_finite_targets_le {count : Nat}
    (targets : Fin count → FullOutput256) :
    uniformFullOutput256.toOuterMeasure
        (finiteTargets targets : Set FullOutput256) ≤
      (count : ENNReal) / ((2 : ENNReal) ^ 256) := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [uniformFullOutput256, PMF.uniformOfFintype_apply,
    Finset.sum_const, nsmul_eq_mul]
  rw [show (Fintype.card FullOutput256 : ENNReal) =
    (2 : ENNReal) ^ 256 by norm_num [FullOutput256]]
  rw [div_eq_mul_inv]
  exact mul_le_mul_right' (by exact_mod_cast finiteTargets_card_le targets) _

/-- Conditional collision lemma used at one fresh-oracle exposure: once the
prior answers are fixed, a new uniform 256-bit answer hits one of `count`
recorded answers with probability at most `count / 2^256`. -/
theorem uniform_full_output_collision_with_previous_le {count : Nat}
    (previousAnswers : Fin count → FullOutput256) :
    uniformFullOutput256.toOuterMeasure
        (finiteTargets previousAnswers : Set FullOutput256) ≤
      (count : ENNReal) / ((2 : ENNReal) ^ 256) :=
  uniform_full_output_hits_finite_targets_le previousAnswers

/-- A directly usable quadratic target family.  The extra target is kept
visible because it is the `+1` in the BCS hash-chain accounting. -/
theorem uniform_full_output_quadratic_targets_le (oracleQueries : Nat)
    (targets : Fin (oracleQueries ^ 2 + 1) → FullOutput256) :
    uniformFullOutput256.toOuterMeasure
        (finiteTargets targets : Set FullOutput256) ≤
      (((oracleQueries : ENNReal) ^ 2) + 1) /
        ((2 : ENNReal) ^ 256) := by
  simpa [Nat.cast_add, Nat.cast_pow] using
    (uniform_full_output_hits_finite_targets_le targets)

theorem three_event_union_probability_le
    {Sample : Type*} (law : PMF Sample) (first second third : Set Sample) :
    law.toOuterMeasure (first ∪ second ∪ third) ≤
      law.toOuterMeasure first + law.toOuterMeasure second +
        law.toOuterMeasure third := by
  calc
    law.toOuterMeasure (first ∪ second ∪ third) ≤
        law.toOuterMeasure (first ∪ second) + law.toOuterMeasure third :=
      measure_union_le _ _
    _ ≤ (law.toOuterMeasure first + law.toOuterMeasure second) +
        law.toOuterMeasure third :=
      add_le_add_left (measure_union_le first second) _
    _ = law.toOuterMeasure first + law.toOuterMeasure second +
        law.toOuterMeasure third := rfl

theorem three_quadratic_events_le_bcs_numerator
    {Sample : Type*} (law : PMF Sample)
    (first second third : Set Sample) (oracleQueries : Nat)
    (firstBound : law.toOuterMeasure first ≤
      (((oracleQueries : ENNReal) ^ 2) + 1) / ((2 : ENNReal) ^ 256))
    (secondBound : law.toOuterMeasure second ≤
      (((oracleQueries : ENNReal) ^ 2) + 1) / ((2 : ENNReal) ^ 256))
    (thirdBound : law.toOuterMeasure third ≤
      (((oracleQueries : ENNReal) ^ 2) + 1) / ((2 : ENNReal) ^ 256)) :
    law.toOuterMeasure (first ∪ second ∪ third) ≤
      3 * (((oracleQueries : ENNReal) ^ 2) + 1) /
        ((2 : ENNReal) ^ 256) := by
  calc
    law.toOuterMeasure (first ∪ second ∪ third) ≤
        law.toOuterMeasure first + law.toOuterMeasure second +
          law.toOuterMeasure third :=
      three_event_union_probability_le law first second third
    _ ≤ ((((oracleQueries : ENNReal) ^ 2) + 1) /
          ((2 : ENNReal) ^ 256)) +
        ((((oracleQueries : ENNReal) ^ 2) + 1) /
          ((2 : ENNReal) ^ 256)) +
        ((((oracleQueries : ENNReal) ^ 2) + 1) /
          ((2 : ENNReal) ^ 256)) :=
      add_le_add (add_le_add firstBound secondBound) thirdBound
    _ = 3 * (((oracleQueries : ENNReal) ^ 2) + 1) /
        ((2 : ENNReal) ^ 256) := by
      simp only [div_eq_mul_inv]
      ring

/-- BCS-shaped finite-output benchmark for one adaptive lazy-oracle bad event.
It is a definition, not a field, axiom, theorem premise, or claimed Tag-73
result. Literal BCS applicability has failed, so even a proof of this bound
would still need the query-DAG/forest coupling and could require additional
Tag-specific events. The three work predicates are absent: selected work
nonces and transcript absorbs stay in the execution, while only the work
predicates are erased in the separate deterministic acceptance refinement. -/
def AdaptiveHashChainProbabilityLemmaNeeded
    {Sample : Type*} (law : PMF Sample) (adaptiveHashChainBad : Set Sample)
    (oracleQueries : Nat) : Prop :=
  law.toOuterMeasure adaptiveHashChainBad ≤
    3 * (((oracleQueries : ENNReal) ^ 2) + 1) /
      ((2 : ENNReal) ^ 256)

#print axioms splitAtDrivingQuery_success
#print axioms makeSameTapeExperimentOrigin_identity
#print axioms makeSameTapeExperimentOrigin_first_execution
#print axioms makeSameTapeExperimentOrigin_same_hidden_tape_start
#print axioms makeSameTapeExperimentOrigin_first_run_state
#print axioms makeSameTapeExperimentOrigin_initialOracle
#print axioms fixedFirstRunRecordFromOrigin_observation
#print axioms fixedFirstRunRecordFromOrigin_firstRun
#print axioms constructLegalReplayFromOrigin_unfold
#print axioms map_success_is_operational
#print axioms map_success_preserves_identity_q1_pause_history_resources
#print axioms map_from_origin_success_preserves_identity_q1_pause_history_resources
#print axioms prefix_run_history_is_preserved
#print axioms postfork_run_history_is_preserved
#print axioms full_output_256_cardinality
#print axioms digest256EquivFinByteVector_apply
#print axioms fin_byte_vector_256_cardinality
#print axioms deployed_digest_256_cardinality
#print axioms uniform_full_output_point_mass
#print axioms uniform_full_output_guess_probability
#print axioms transported_uniform_digest_singleton_probability
#print axioms transported_uniform_digest_point_mass
#print axioms uniform_digest_point_mass
#print axioms transported_uniform_digest_eq_uniform
#print axioms uniform_full_output_hits_finite_targets_le
#print axioms uniform_full_output_collision_with_previous_le
#print axioms uniform_full_output_quadratic_targets_le
#print axioms three_event_union_probability_le
#print axioms three_quadratic_events_le_bcs_numerator

end AspisK1.V7FsStateRestorationCoupling
