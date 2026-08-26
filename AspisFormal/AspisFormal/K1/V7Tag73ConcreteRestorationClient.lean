import AspisFormal.K1.V7Tag73SchedulerNativeResult
import AspisFormal.K1.V7Tag73RawStrictReplacementSuffix

/-!
# Concrete finite restoration client for the Tag-73 scheduler

This module is the operational dispatcher between a black-box extractor and
the result-carrying uniform scheduler.  A client can request only a node that
is already in the concrete store and a transition index in that node's actual
future-free verifier history.  The interpreter itself:

* reads that transition and rejects non-squeeze transitions;
* derives both SHA inputs and the complete verifier checkpoint from the
  transition's `before` snapshot;
* replays the same hidden-tape prover from its literal start to the first
  occurrence of either input;
* obtains the two programmed answers from one scheduler-native `forkPair`;
* discards the stale suffix and performs a complete second run from the same
  literal start over the prefix-derived programmed oracle; and
* runs the raw future-free verifier from the exact restored checkpoint.

The accumulator contains only plain execution data, failure records, and an
append-only resource-charge log.  It has no proof fields, restore function,
controller, trace cover, acceptance inclusion, outcome/world function, or
extractor conclusion.  Proofs about nodes are stated separately.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ConcreteRestorationClient

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73RawStrictReplacementSuffix

noncomputable section

universe u v

/-! ## Client language and plain runtime data -/

/-- The extractor can name only an existing node and a literal index in that
node's verifier transition list.  It cannot supply a snapshot or SHA input. -/
structure ConcreteRestorationRequest where
  nodeId : Nat
  verifierTransitionIndex : Nat
  deriving DecidableEq, Repr

inductive ConcreteRestorationFailure where
  | restorationFuelExhausted
  | unknownNode
  | unknownVerifierTransition
  | transitionIsNotSqueeze
  | prefixReturnedEarly
  | prefixOracleAbort (reason : OracleAbort)
  | prefixDidNotPauseAtSelectedQuery
  | prefixTraceMismatch
  | incoherentPrefixOracle
  | incoherentProgrammedOracle
  | globalLimitTooSmall
  | pairExposureLimit
  | pairInputsAliased
  | outputInputAlreadyDefined
  | advanceInputAlreadyDefined
  | pairProgrammingAbort (half : SqueezeHalf) (reason : OracleAbort)
  | proverReplayRoom
  | proverReplayAbort (reason : OracleAbort)
  | proverReplayTimeout
  | restoredBindingMismatch
  | verifierSuffixRoom
  | verifierSuffixAbort (reason : OracleAbort)
  | verifierSuffixTimeout
  deriving DecidableEq, Repr

inductive ConcreteRestorationReply where
  | added (nodeId : Nat)
  | failed (reason : ConcreteRestorationFailure)
  deriving DecidableEq, Repr

/-- A finite free client.  The only effect is one concrete restoration
request; all branching on its reply remains ordinary client computation. -/
inductive ConcreteRestorationClient (Result : Type u) where
  | pure (result : Result)
  | restore (request : ConcreteRestorationRequest)
      (next : ConcreteRestorationReply → ConcreteRestorationClient Result)

/-- An oracle state boundary and both actual machine results for one complete
from-start prover node followed by its restored future-free verifier suffix.
Every field is runtime data. -/
structure ConcreteRestorationNode
    (Statement Proof Payload : Type*) where
  parentRequest : Option ConcreteRestorationRequest
  adversaryValue :
    CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  proverEntryOracle : OracleState
  proverFinalOracle : OracleState
  verifierEntryOracle : OracleState
  verifierFinalOracle : OracleState
  verifierEntryState : FutureFreeVerifierState
  verifierFinalState : FutureFreeVerifierState

def ConcreteRestorationNode.proverHistory
    {Statement Proof Payload : Type*}
    (node : ConcreteRestorationNode Statement Proof Payload) :
    List QueryRecord :=
  historySince node.proverEntryOracle node.proverFinalOracle

def ConcreteRestorationNode.verifierHistory
    {Statement Proof Payload : Type*}
    (node : ConcreteRestorationNode Statement Proof Payload) :
    List QueryRecord :=
  historySince node.verifierEntryOracle node.verifierFinalOracle

/-- Append-only charges.  Keeping the components separate prevents a later
proof from silently equating a programming coordinate, an oracle query, and a
verifier microstep. -/
inductive ConcreteRestorationCharge where
  | prefixReplayQueries (count : Nat)
  | forkUniformCoordinates (count : Nat)
  | programmedPoints (count : Nat)
  | completeFromStartQueries (count : Nat)
  | verifierSuffixQueries (count : Nat)
  | verifierTransitions (count : Nat)
  | restart (count : Nat)
  deriving DecidableEq, Repr

def ConcreteRestorationCharge.oracleQueries :
    ConcreteRestorationCharge → Nat
  | .prefixReplayQueries count => count
  | .completeFromStartQueries count => count
  | .verifierSuffixQueries count => count
  | _ => 0

def ConcreteRestorationCharge.uniformForkCoordinates :
    ConcreteRestorationCharge → Nat
  | .forkUniformCoordinates count => count
  | _ => 0

def ConcreteRestorationCharge.successfulProgrammingPoints :
    ConcreteRestorationCharge → Nat
  | .programmedPoints count => count
  | _ => 0

def ConcreteRestorationCharge.restarts :
    ConcreteRestorationCharge → Nat
  | .restart count => count
  | _ => 0

def ConcreteRestorationCharge.protocolTransitions :
    ConcreteRestorationCharge → Nat
  | .verifierTransitions count => count
  | _ => 0

structure ConcreteRestorationFailureRecord where
  request : ConcreteRestorationRequest
  reason : ConcreteRestorationFailure
  deriving DecidableEq, Repr

/-- No proof is stored in the live accumulator.  Its exactness is established
by induction over the interpreter below. -/
structure ConcreteRestorationAccumulator
    (Statement Proof Payload : Type*) where
  nodes : List (ConcreteRestorationNode Statement Proof Payload)
  failures : List ConcreteRestorationFailureRecord
  charges : List ConcreteRestorationCharge

def ConcreteRestorationAccumulator.node?
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (nodeId : Nat) : Option (ConcreteRestorationNode Statement Proof Payload) :=
  accumulator.nodes[nodeId]?

def ConcreteRestorationAccumulator.addCharges
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge) :
    ConcreteRestorationAccumulator Statement Proof Payload :=
  { accumulator with charges := accumulator.charges ++ charges }

def ConcreteRestorationAccumulator.addFailure
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure) :
    ConcreteRestorationAccumulator Statement Proof Payload :=
  { accumulator with
    failures := accumulator.failures ++ [{ request := request, reason := reason }] }

def ConcreteRestorationAccumulator.addNode
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (node : ConcreteRestorationNode Statement Proof Payload) :
    Nat × ConcreteRestorationAccumulator Statement Proof Payload :=
  (accumulator.nodes.length,
    { accumulator with nodes := accumulator.nodes ++ [node] })

def ConcreteRestorationAccumulator.oracleQueryTotal
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Nat :=
  (accumulator.charges.map ConcreteRestorationCharge.oracleQueries).sum

def ConcreteRestorationAccumulator.uniformForkCoordinateTotal
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Nat :=
  (accumulator.charges.map
    ConcreteRestorationCharge.uniformForkCoordinates).sum

def ConcreteRestorationAccumulator.programmedPointTotal
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Nat :=
  (accumulator.charges.map
    ConcreteRestorationCharge.successfulProgrammingPoints).sum

def ConcreteRestorationAccumulator.restartTotal
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Nat :=
  (accumulator.charges.map ConcreteRestorationCharge.restarts).sum

def ConcreteRestorationAccumulator.verifierTransitionTotal
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Nat :=
  (accumulator.charges.map
    ConcreteRestorationCharge.protocolTransitions).sum

theorem add_charges_oracle_query_total
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge) :
    (accumulator.addCharges charges).oracleQueryTotal =
      accumulator.oracleQueryTotal +
        (charges.map ConcreteRestorationCharge.oracleQueries).sum := by
  simp [ConcreteRestorationAccumulator.addCharges,
    ConcreteRestorationAccumulator.oracleQueryTotal]

theorem add_charges_programmed_point_total
    {Statement Proof Payload : Type*}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge) :
    (accumulator.addCharges charges).programmedPointTotal =
      accumulator.programmedPointTotal +
        (charges.map
          ConcreteRestorationCharge.successfulProgrammingPoints).sum := by
  simp [ConcreteRestorationAccumulator.addCharges,
    ConcreteRestorationAccumulator.programmedPointTotal]

/-! ## Root construction and actual transition selection -/

/-- The root node is a projection of one actual two-phase execution.  In
particular, neither verifier state can be supplied separately by the caller. -/
def rootRestorationNode
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    ConcreteRestorationNode Statement Proof Payload where
  parentRequest := none
  adversaryValue := execution.adversaryValue
  proverEntryOracle := source.initialOracle
  proverFinalOracle := source.firstExecution.oracle
  verifierEntryOracle := source.firstExecution.oracle
  verifierFinalOracle := execution.verifierRun.oracle
  verifierEntryState := initialFutureFreeVerifierState
    (FixedBindings.ofContext execution.adversaryValue.rawMessages.context)
  verifierFinalState := execution.finalState

def initialRestorationAccumulator
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    ConcreteRestorationAccumulator Statement Proof Payload where
  nodes := [rootRestorationNode execution]
  failures := []
  charges := []

/-- Scheduler-native entry form.  The root is runtime data constructed by the
initial prover/verifier dispatcher; no execution equation is stored in the
live accumulator. -/
def initialRestorationAccumulatorFromRoot
    {Statement Proof Payload : Type*}
    (root : ConcreteRestorationNode Statement Proof Payload) :
    ConcreteRestorationAccumulator Statement Proof Payload where
  nodes := [root]
  failures := []
  charges := []

@[simp] theorem initial_accumulator_from_root_is_singleton
    {Statement Proof Payload : Type*}
    (root : ConcreteRestorationNode Statement Proof Payload) :
    (initialRestorationAccumulatorFromRoot root).nodes = [root] := by
  rfl

@[simp] theorem initial_accumulator_root_is_exact_execution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    (initialRestorationAccumulator execution).nodes =
      [rootRestorationNode execution] := by
  rfl

def verifierTransitionAt?
    {Statement Proof Payload : Type*}
    (node : ConcreteRestorationNode Statement Proof Payload)
    (index : Nat) : Option FutureFreeTransition :=
  node.verifierFinalState.transitions[index]?

/-- Restore only to the actual `before` snapshot carried by the selected
transition.  The singleton `seen` list is the required nonempty verifier
state; no stale transition suffix is retained. -/
def restoreIndexedTransition
    (transition : FutureFreeTransition) : FutureFreeVerifierState where
  current := transition.before
  seen := [transition.before]
  transitions := []

@[simp] theorem restore_indexed_transition_is_nonempty
    (transition : FutureFreeTransition) :
    (restoreIndexedTransition transition).seen ≠ [] := by
  simp [restoreIndexedTransition]

@[simp] theorem restore_indexed_transition_current
    (transition : FutureFreeTransition) :
    (restoreIndexedTransition transition).current = transition.before := by
  rfl

/-- Locality of the raw driver at a restored verifier action: whenever the
live control has a forced verifier action, no prover-owned field is submitted
first.  In particular a restored squeeze consumes its programmed pair before
the driver can consult any later raw response.  This theorem requires no
equality between unused earlier fields of two whole raw returns. -/
theorem next_verifier_action_excludes_raw_submission
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (action : VerifierAction)
    (forced : state.current.control.nextVerifierAction? = some action) :
    submitNextRawMessage raw state = none := by
  cases controlEq : state.current.control with
  | adaptive control =>
      cases control <;>
        simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?,
          OpenAdaptiveControl.nextVerifierAction?]
  | linear remaining =>
      cases remaining with
      | nil =>
          simp_all [submitNextRawMessage,
            FutureFreeControl.nextVerifierAction?]
      | cons slot rest =>
          cases slot <;>
            simp_all [submitNextRawMessage,
              FutureFreeControl.nextVerifierAction?]
  | absorbPayload payload remaining =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | workCheck stage nonce remaining =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | workCheckpoint stage nonce remaining =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | workAbsorb stage nonce remaining =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | sampleChallenge id outputs remaining =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | q16Absorb base counter remaining =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | q16Sample base counter outputs remaining =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | q16Restore base counter nextCounter remaining =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | q16Selected base counter schedule remaining =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | q16SamplerReject counter reason =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | q16AllNoncompactReject =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | rejected reason =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]
  | done =>
      simp_all [submitNextRawMessage, FutureFreeControl.nextVerifierAction?]

/-- Therefore the first driver microstep at a restored squeeze is literally
the verifier action program; earlier raw fields are not even inspected by the
driver branch. -/
theorem raw_microstep_at_forced_verifier_action
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state : FutureFreeVerifierState) (action : VerifierAction)
    (forced : state.current.control.nextVerifierAction? = some action) :
    rawFutureFreeMicrostep environment raw state =
      runOneFutureFreeVerifierAction environment state := by
  simp [rawFutureFreeMicrostep,
    next_verifier_action_excludes_raw_submission raw state action forced]

/-! ## Deterministic prefix preparation -/

structure PreparedConcreteRestoration
    (Statement Proof Payload : Type*) where
  request : ConcreteRestorationRequest
  parentNode : ConcreteRestorationNode Statement Proof Payload
  transition : FutureFreeTransition
  restoredState : FutureFreeVerifierState
  outputInput : ShaInput
  advanceInput : ShaInput
  /-- `none` is the legal absent-pair branch.  In that branch the programming
  base is the actual end of the complete parent prover segment. -/
  occurrence : Option PairOccurrenceSplit
  prefixRun : Option (PrefixRun
    (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
  programmingBase : OracleState
  prefixSteps : Nat

inductive ConcretePreparationResult
    (Statement Proof Payload : Type*) where
  | failed (reason : ConcreteRestorationFailure) (prefixSteps : Nat)
      (prefixRestarts : Nat)
  | ready (prepared : PreparedConcreteRestoration Statement Proof Payload)

structure ConcreteRestorationConfiguration where
  oracleLimits : OracleLimits
  pairProgrammingOrder : PairProgrammingOrder
  proverReplayFuel : Nat
  driverFuel : Nat
  verifierFuel : Nat

/-- Validate an extractor request and replay only the recorded prefix.  This
computation reads no fresh scheduler coordinate. -/
def prepareConcreteRestorationFromStartProgram
    {Statement Proof Payload : Type*}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest) :
    ConcretePreparationResult Statement Proof Payload :=
  match accumulator.node? request.nodeId with
  | none => .failed .unknownNode 0 0
  | some parentNode =>
      match verifierTransitionAt? parentNode
          request.verifierTransitionIndex with
      | none => .failed .unknownVerifierTransition 0 0
      | some transition =>
          match squeezePairInputsOfTransition transition with
          | none => .failed .transitionIsNotSqueeze 0 0
          | some (outputInput, advanceInput) =>
              match firstEitherInputOccurrence outputInput advanceInput
                  parentNode.proverHistory with
              | none =>
                  .ready
                    { request := request
                      parentNode := parentNode
                      transition := transition
                      restoredState := restoreIndexedTransition transition
                      outputInput := outputInput
                      advanceInput := advanceInput
                      occurrence := none
                      prefixRun := none
                      programmingBase := parentNode.proverFinalOracle
                      prefixSteps := 0 }
              | some occurrence =>
                  let prefixRun := runPrefix
                    (recordedPrefixController
                      parentNode.proverEntryOracle.history.length
                      occurrence.before)
                    configuration.oracleLimits .extractorReplay
                    occurrence.before.length parentNode.proverEntryOracle
                    startProgram
                  match prefixRun.halt with
                  | .returned _ =>
                      .failed .prefixReturnedEarly prefixRun.steps 1
                  | .oracleAbort reason =>
                      .failed (.prefixOracleAbort reason) prefixRun.steps 1
                  | .paused residual =>
                      match residual with
                      | .pure _ | .abort _ =>
                          .failed .prefixDidNotPauseAtSelectedQuery
                            prefixRun.steps 1
                      | .query pendingInput _next =>
                          if pendingMismatch :
                              pendingInput ≠ occurrence.chosen.input then
                            .failed .prefixDidNotPauseAtSelectedQuery
                              prefixRun.steps 1
                          else if traceMismatch : queryAnswerTrace
                              (historySince parentNode.proverEntryOracle
                                prefixRun.oracle) ≠
                                queryAnswerTrace occurrence.before then
                            .failed .prefixTraceMismatch prefixRun.steps 1
                          else
                            .ready
                              { request := request
                                parentNode := parentNode
                                transition := transition
                                restoredState :=
                                  restoreIndexedTransition transition
                                outputInput := outputInput
                                advanceInput := advanceInput
                                occurrence := some occurrence
                                prefixRun := some prefixRun
                                programmingBase := prefixRun.oracle
                                prefixSteps := prefixRun.steps }

/-- Compatibility entry for a conventional raw same-tape source.  Prefix
preparation reads only the source's one closed literal start program. -/
def prepareConcreteRestoration
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest) :
    ConcretePreparationResult Statement Proof Payload :=
  prepareConcreteRestorationFromStartProgram
    (source.capability.start source.observation) configuration accumulator
      request

/-! ## Pair programming without a post-fork controller -/

inductive ConcretePairProgrammingResult where
  | failed (reason : ConcreteRestorationFailure)
      (successfullyProgrammed : Nat)
  | ready (afterBoth : OracleState)

def programConcreteHalf
    (limits : OracleLimits) (state : OracleState)
    (input : ShaInput) (output : ShaOutput) : Except OracleAbort OracleState :=
  programOracle limits .extractorReplay state
    { input := input, output := output }

/-- The two coordinates are inserted only after both target inputs have been
fixed by prefix preparation.  The supplied digests are scheduler outputs,
not client fields. -/
def programConcretePair
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256) : ConcretePairProgrammingResult :=
  if outputInput = advanceInput then
    .failed .pairInputsAliased 0
  else if (lookupEntry state outputInput).isSome then
    .failed .outputInputAlreadyDefined 0
  else if (lookupEntry state advanceInput).isSome then
    .failed .advanceInputAlreadyDefined 0
  else
    let programFirstSecond
        (firstHalf secondHalf : SqueezeHalf)
        (firstInput secondInput : ShaInput)
        (firstOutput secondOutput : ShaOutput) :=
      match programConcreteHalf limits state firstInput firstOutput with
      | .error reason =>
          .failed (.pairProgrammingAbort firstHalf reason) 0
      | .ok afterFirst =>
          match programConcreteHalf limits afterFirst secondInput
              secondOutput with
          | .error reason =>
              .failed (.pairProgrammingAbort secondHalf reason) 1
          | .ok afterBoth => .ready afterBoth
    match order with
    | .outputThenAdvance =>
        programFirstSecond .output .advance outputInput advanceInput
          forkOutput forkAdvance
    | .advanceThenOutput =>
        programFirstSecond .advance .output advanceInput outputInput
          forkAdvance forkOutput

/-! ## Totalized machine stages -/

inductive TotalizedMachineFailure where
  | oracleAbort (reason : OracleAbort)
  | timeout
  deriving DecidableEq, Repr

/-- Replace explicit program abort and query-fuel exhaustion by ordinary
return values.  Thus a scheduler callback can append the exact failure to the
runtime accumulator.  Lazy-oracle resource aborts remain scheduler failures;
the dispatcher checks room before entering each stage. -/
def totalizeOracleMachine {Result : Type*} :
    Nat → OracleMachine Result →
      OracleMachine (Except TotalizedMachineFailure Result)
  | _fuel, .pure result => .pure (.ok result)
  | _fuel, .abort reason => .pure (.error (.oracleAbort reason))
  | 0, .query _input _next => .pure (.error .timeout)
  | fuel + 1, .query input next =>
      .query input fun output => totalizeOracleMachine fuel (next output)

/-- Universe-polymorphic result map for an oracle program. -/
def mapOracleMachineResult {Input : Type u} {Output : Type v}
    (map : Input → Output) : OracleMachine Input → OracleMachine Output
  | .pure result => .pure (map result)
  | .abort reason => .abort reason
  | .query input next =>
      .query input fun output => mapOracleMachineResult map (next output)

/-- `SchedulerNativeCursor.machine` deliberately keeps its internal result at
the same universe as the final cursor result.  This proof-free wrapper raises
a smaller protocol-stage result to that universe by carrying the final result
type as a phantom parameter. -/
inductive SchedulerStageResult (Final : Type u) (Payload : Type v) :
    Type (max u v) where
  | completed (payload : Payload)

def schedulerStageProgram (Final : Type u) {Payload : Type v}
    (program : OracleMachine Payload) :
    OracleMachine (SchedulerStageResult Final Payload) :=
  mapOracleMachineResult SchedulerStageResult.completed program

def StageHasOracleRoom (limits : OracleLimits)
    (state : OracleState) (fuel : Nat) : Prop :=
  state.totalCalls + fuel ≤ limits.totalCalls ∧
    state.freshCalls + fuel ≤ limits.freshCalls

local instance stageHasOracleRoomDecidable
    (limits : OracleLimits) (state : OracleState) (fuel : Nat) :
    Decidable (StageHasOracleRoom limits state fuel) := by
  unfold StageHasOracleRoom
  infer_instance

/-! ## Canonical scheduler template -/

def zeroDigest256 : Digest256 := fun _index => 0

def refusingController : AdaptiveController :=
  fun _history _input => .refuse

def zeroResourceUse : ResourceUse where
  adversaryOracleCalls := 0
  simulatorOracleCalls := 0
  verifierOracleCalls := 0
  extractorOracleCalls := 0
  freshOracleAnswers := 0
  programmedPoints := 0
  simulatedProofs := 0
  restartCount := 0
  runtimeSteps := 0
  batchGrindingQueries := 0
  foldGrindingQueries := 0
  finalGrindingQueries := 0
  queryCandidateBranches := 0

def zeroResourceBudget : ResourceBudget where
  adversaryOracleCalls := 0
  simulatorOracleCalls := 0
  verifierOracleCalls := 0
  extractorOracleCalls := 0
  freshOracleAnswers := 0
  programmedPoints := 0
  simulatedProofs := 0
  restartCount := 0
  runtimeSteps := 0
  batchGrindingQueries := 0
  foldGrindingQueries := 0
  finalGrindingQueries := 0
  queryCandidateBranches := 0

/-- `AtomicPairReplayConfiguration` is only the legacy carrier expected by the
uniform pair scheduler.  This interpreter never reads `postForkController`,
`firstRunUse`, `budget`, or `replayFuel`; its own machine phases are native
scheduler nodes.  Hence those fields are fixed canonically rather than
accepted from the client. -/
def canonicalForkTemplate
    (configuration : ConcreteRestorationConfiguration) :
    AtomicPairReplayConfiguration where
  forkOutput := zeroDigest256
  forkAdvance := zeroDigest256
  programmingOrder := configuration.pairProgrammingOrder
  postForkController := refusingController
  oracleLimits := configuration.oracleLimits
  replayFuel := 0
  firstRunUse := zeroResourceUse
  budget := zeroResourceBudget

@[simp] theorem canonical_scheduled_fork_uses_exact_coordinates
    (configuration : ConcreteRestorationConfiguration)
    (forkOutput forkAdvance : Digest256) :
    let scheduled := scheduledForkConfiguration
      (canonicalForkTemplate configuration) forkOutput forkAdvance
    scheduled.forkOutput = forkOutput ∧
      scheduled.forkAdvance = forkAdvance := by
  exact scheduled_fork_configuration_coordinates
    (canonicalForkTemplate configuration) forkOutput forkAdvance

/-! ## Scheduler-native dispatcher -/

inductive ConcreteRestorationClientHalt (Result : Type u) where
  | returned (result : Result)
  | restorationFuelExhausted

structure ConcreteRestorationClientRun
    (Statement Proof Payload : Type*) (Result : Type u) where
  halt : ConcreteRestorationClientHalt Result
  accumulator : ConcreteRestorationAccumulator Statement Proof Payload

private def continueWithFailure
    {Statement Proof Payload Result : Type*} {globalOracleCalls : Nat}
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)) :
    SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) :=
  let failed := accumulator.addFailure request reason
  resume (.failed reason) failed

private def dispatchPreparedRestoration
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)) :
    SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) := by
  classical
  let prefixRestarts := if prepared.prefixRun.isSome then 1 else 0
  let withPrefix := accumulator.addCharges
    [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
  exact if prefixCoherent : HistoryTotalCoherent prepared.programmingBase then
    if globalLimit : configuration.oracleLimits.totalCalls ≤ globalOracleCalls then
      if pairRoom : prepared.programmingBase.history.length + 2 ≤
          globalOracleCalls then
        .forkPair prepared.programmingBase.history pairRoom
          prepared.outputInput prepared.advanceInput
          (canonicalForkTemplate configuration)
          (fun forkConfiguration =>
            let afterCoordinates := withPrefix.addCharges
              [.forkUniformCoordinates 2]
            match programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                forkConfiguration.forkOutput forkConfiguration.forkAdvance with
            | .failed reason inserted =>
                continueWithFailure prepared.request reason
                  (afterCoordinates.addCharges [.programmedPoints inserted])
                  resume
            | .ready afterBoth =>
                let afterProgramming := afterCoordinates.addCharges
                  [.programmedPoints 2]
                if afterCoherent : HistoryTotalCoherent afterBoth then
                  if proverRoom : StageHasOracleRoom configuration.oracleLimits
                      afterBoth configuration.proverReplayFuel then
                    let atProverStart := afterProgramming.addCharges
                      [.restart 1]
                    .machine configuration.oracleLimits globalLimit
                      .extractorReplay afterBoth
                      (schedulerStageProgram
                        (ConcreteRestorationClientRun Statement Proof Payload
                          Result)
                        (totalizeOracleMachine configuration.proverReplayFuel
                          startProgram))
                      configuration.proverReplayFuel afterCoherent
                      (fun (proverStage : SchedulerStageResult
                            (ConcreteRestorationClientRun Statement Proof Payload
                              Result)
                            (Except TotalizedMachineFailure
                              (CheckedRawTag73AdversaryReturnedValue Statement
                                Proof Payload)))
                          (proverFinalOracle : OracleState)
                          (proverCoherent :
                            HistoryTotalCoherent proverFinalOracle) =>
                      match proverStage with
                      | .completed proverResult =>
                      let proverQueries :=
                        (historySince afterBoth proverFinalOracle).length
                      let afterProver := atProverStart.addCharges
                        [.completeFromStartQueries proverQueries]
                      match proverResult with
                      | .error (.oracleAbort reason) =>
                          continueWithFailure prepared.request
                            (.proverReplayAbort reason) afterProver resume
                      | .error .timeout =>
                          continueWithFailure prepared.request
                            .proverReplayTimeout afterProver resume
                      | .ok adversaryValue =>
                          let rawMessages :=
                            CheckedRawTag73AdversaryReturnedValue.rawMessages
                              adversaryValue
                          if bindingMismatch :
                              FixedBindings.ofContext
                                  rawMessages.context ≠
                                prepared.restoredState.current.bindings then
                            continueWithFailure prepared.request
                              .restoredBindingMismatch afterProver resume
                          else if verifierRoom : StageHasOracleRoom
                              configuration.oracleLimits proverFinalOracle
                              configuration.verifierFuel then
                            .machine configuration.oracleLimits globalLimit
                              .verifier proverFinalOracle
                              (schedulerStageProgram
                                (ConcreteRestorationClientRun Statement Proof
                                  Payload Result)
                                (totalizeOracleMachine
                                  configuration.verifierFuel
                                  (driveRawFutureFree environment rawMessages
                                    configuration.driverFuel
                                    prepared.restoredState)))
                              configuration.verifierFuel proverCoherent
                              (fun (verifierStage : SchedulerStageResult
                                    (ConcreteRestorationClientRun Statement
                                      Proof Payload Result)
                                    (Except TotalizedMachineFailure
                                      FutureFreeVerifierState))
                                  (verifierFinalOracle : OracleState)
                                  (_verifierCoherent :
                                    HistoryTotalCoherent verifierFinalOracle) =>
                                match verifierStage with
                                | .completed verifierResult =>
                                let verifierQueries :=
                                  (historySince proverFinalOracle
                                    verifierFinalOracle).length
                                let afterVerifier := afterProver.addCharges
                                  [.verifierSuffixQueries verifierQueries]
                                match verifierResult with
                                | .error (.oracleAbort reason) =>
                                    continueWithFailure prepared.request
                                      (.verifierSuffixAbort reason)
                                      afterVerifier resume
                                | .error .timeout =>
                                    continueWithFailure prepared.request
                                      .verifierSuffixTimeout afterVerifier
                                      resume
                                | .ok verifierFinalState =>
                                    let transitionCount :=
                                      verifierFinalState.transitions.length
                                    let node : ConcreteRestorationNode
                                        Statement Proof Payload :=
                                      { parentRequest := some prepared.request
                                        adversaryValue := adversaryValue
                                        proverEntryOracle := afterBoth
                                        proverFinalOracle := proverFinalOracle
                                        verifierEntryOracle := proverFinalOracle
                                        verifierFinalOracle := verifierFinalOracle
                                        verifierEntryState :=
                                          prepared.restoredState
                                        verifierFinalState :=
                                          verifierFinalState }
                                    let charged := afterVerifier.addCharges
                                      [.verifierTransitions transitionCount]
                                    let added := charged.addNode node
                                    resume (.added added.1) added.2)
                          else
                            continueWithFailure prepared.request
                              .verifierSuffixRoom afterProver resume)
                  else
                    continueWithFailure prepared.request .proverReplayRoom
                      afterProgramming resume
                else
                  continueWithFailure prepared.request
                    .incoherentProgrammedOracle
                    afterProgramming resume)
      else
        continueWithFailure prepared.request .pairExposureLimit withPrefix
          resume
    else
      continueWithFailure prepared.request .globalLimitTooSmall withPrefix
        resume
  else
    continueWithFailure prepared.request .incoherentPrefixOracle withPrefix
      resume

private def dispatchConcreteRestoration
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)) :
    SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) :=
  match prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request with
  | .failed reason prefixSteps prefixRestarts =>
      continueWithFailure request reason
        (accumulator.addCharges
          [.prefixReplayQueries prefixSteps, .restart prefixRestarts]) resume
  | .ready prepared =>
      dispatchPreparedRestoration startProgram environment configuration prepared
        accumulator resume

/-- One checked layer of the concrete client interpreter.  This wrapper is
public only so the induction theorem below can state its step case without
exposing the private recursive runner.  It performs the actual preparation,
failure recording, fork request, programming, prover replay, verifier suffix,
and continuation dispatch defined above; it is not a caller-supplied handler.
-/
def dispatchOneConcreteRestoration
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)) :
    SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) :=
  dispatchConcreteRestoration startProgram environment configuration
    accumulator request resume

/-- Total fuel-bounded interpreter.  The recursive call consumes one
restoration-fuel unit before any asynchronous scheduler stage is installed. -/
private def runConcreteRestorationClient
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration) :
    Nat → ConcreteRestorationAccumulator Statement Proof Payload →
      ConcreteRestorationClient Result →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result)
  | _fuel, accumulator, .pure result =>
      .returned { halt := .returned result, accumulator := accumulator }
  | 0, accumulator, .restore request _next =>
      let failed := accumulator.addFailure request .restorationFuelExhausted
      .returned
        { halt := .restorationFuelExhausted
          accumulator := failed }
  | fuel + 1, accumulator, .restore request next =>
      dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request
        (fun reply nextAccumulator =>
          runConcreteRestorationClient startProgram environment configuration fuel
            nextAccumulator (next reply))

private theorem run_concrete_restoration_client_induction_aux
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (motive : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) → Prop)
    (terminal : ∀ run, motive (.returned run))
    (requestStep : ∀
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (request : ConcreteRestorationRequest)
      (resume : ConcreteRestorationReply →
        ConcreteRestorationAccumulator Statement Proof Payload →
          SchedulerNativeCursor globalOracleCalls
            (ConcreteRestorationClientRun Statement Proof Payload Result)),
      (∀ reply nextAccumulator, motive (resume reply nextAccumulator)) →
      motive (dispatchOneConcreteRestoration startProgram environment
        configuration accumulator request resume))
    (fuel : Nat)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (client : ConcreteRestorationClient Result) :
    motive (runConcreteRestorationClient startProgram environment configuration
      fuel accumulator client) := by
  induction fuel generalizing accumulator client with
  | zero =>
      cases client with
      | pure result =>
          exact terminal
            { halt := .returned result, accumulator := accumulator }
      | restore request next =>
          exact terminal
            { halt := .restorationFuelExhausted
              accumulator := accumulator.addFailure request
                .restorationFuelExhausted }
  | succ fuel ih =>
      cases client with
      | pure result =>
          exact terminal
            { halt := .returned result, accumulator := accumulator }
      | restore request next =>
          apply requestStep accumulator request
            (fun reply nextAccumulator =>
              runConcreteRestorationClient startProgram environment
                configuration fuel nextAccumulator (next reply))
          intro reply nextAccumulator
          exact ih nextAccumulator (next reply)

/-- Scheduler-native lower-level entry.  A surrounding cursor constructs the
root from its actual initial prover and verifier callbacks, while every replay
uses this one literal closed start program. -/
def startConcreteRestorationClientFromRoot
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result) :
    SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) :=
  runConcreteRestorationClient startProgram environment configuration
    restorationFuel (initialRestorationAccumulatorFromRoot root) client

/-- Public induction hook for the private fuel-bounded interpreter.  To prove
a property of the actual client cursor, it is enough to prove it for terminal
results and show that the real one-request dispatcher preserves it whenever
all adaptive reply continuations already have it.  No unchecked cursor,
resource fact, or result field is supplied by the caller. -/
theorem start_concrete_restoration_client_from_root_induction
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (motive : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) → Prop)
    (terminal : ∀ run, motive (.returned run))
    (requestStep : ∀
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (request : ConcreteRestorationRequest)
      (resume : ConcreteRestorationReply →
        ConcreteRestorationAccumulator Statement Proof Payload →
          SchedulerNativeCursor globalOracleCalls
            (ConcreteRestorationClientRun Statement Proof Payload Result)),
      (∀ reply nextAccumulator, motive (resume reply nextAccumulator)) →
      motive (dispatchOneConcreteRestoration startProgram environment
        configuration accumulator request resume)) :
    motive (startConcreteRestorationClientFromRoot
      (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration restorationFuel client) := by
  exact run_concrete_restoration_client_induction_aux startProgram environment
    configuration motive terminal requestStep restorationFuel
      (initialRestorationAccumulatorFromRoot root) client

/-- Entry point deriving the initial node store from one actual raw verifier
execution. -/
def startConcreteRestorationClient
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result) :
    SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) :=
  runConcreteRestorationClient
    (source.capability.start source.observation) execution.environment
      configuration restorationFuel
    (initialRestorationAccumulator execution) client

@[simp] theorem start_pure_client_returns_exact_root_accumulator
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat) (result : Result) :
    startConcreteRestorationClient (globalOracleCalls := globalOracleCalls)
      execution configuration restorationFuel (.pure result) =
        .returned
          { halt := .returned result
            accumulator := initialRestorationAccumulator execution } := by
  simp [startConcreteRestorationClient, runConcreteRestorationClient]

@[simp] theorem start_pure_client_from_root_returns_exact_accumulator
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat) (result : Result) :
    startConcreteRestorationClientFromRoot
      (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration restorationFuel (.pure result) =
        .returned
          { halt := .returned result
            accumulator := initialRestorationAccumulatorFromRoot root } := by
  simp [startConcreteRestorationClientFromRoot, runConcreteRestorationClient]

#print axioms initial_accumulator_root_is_exact_execution
#print axioms add_charges_oracle_query_total
#print axioms add_charges_programmed_point_total
#print axioms restore_indexed_transition_is_nonempty
#print axioms next_verifier_action_excludes_raw_submission
#print axioms raw_microstep_at_forced_verifier_action
#print axioms canonical_scheduled_fork_uses_exact_coordinates
#print axioms start_pure_client_returns_exact_root_accumulator
#print axioms initial_accumulator_from_root_is_singleton
#print axioms start_pure_client_from_root_returns_exact_accumulator
#print axioms start_concrete_restoration_client_from_root_induction

end

end AspisK1.V7Tag73ConcreteRestorationClient
