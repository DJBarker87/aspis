import AspisFormal.K1.V7Tag73ConcreteRestorationClient
import AspisFormal.K1.V7Tag73UniformRawVerifierExecution
import AspisFormal.K1.V7Tag73ProjectedFreshController

/-!
# One scheduler-native plain-ROM Tag-73 experiment

This is the operational root missing between the uniform exposure scheduler
and the concrete restoration client.  For one fixed hidden adversary tape it
installs, in order, the literal raw prover start program, the dependent
future-free verifier program built from the value that actually returned, and
then the finite restoration client.  All three phases are nodes of one
`SchedulerNativeCursor`, so one master tape supplies every fresh lazy-oracle
answer and every adjacent programmed-pair coordinate.

The cursor is fixed before that master tape is sampled.  In particular it
does not accept a random-oracle controller, a completed execution, a verifier
state, an outcome/world map, a restoration function, or a trace-cover
premise.  Its root node is constructed only inside the two nested operational
return callbacks.

The projected-controller reconstruction is deliberately a theorem layer
after this runtime construction: fork coordinates are interleaved in the
master tape, so the master tape itself is not an ordinary lazy-oracle
controller.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativePlainRomExperiment

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ProjectedFreshController

noncomputable section

universe u

/-! ## Result functor for the native cursor -/

/-- Change only the final result of a scheduler cursor.  Machine programs,
oracle states, fork targets, actors, limits and adaptive continuations are
retained literally. -/
def mapSchedulerNativeCursorResult
    {globalOracleCalls : Nat} {Input Output : Type u}
    (map : Input → Output) :
    SchedulerNativeCursor globalOracleCalls Input →
      SchedulerNativeCursor globalOracleCalls Output
  | .machine limits limitBound actor state program fuel coherent onReturned =>
      .machine limits limitBound actor state program fuel coherent
        (fun result finalState finalCoherent =>
          mapSchedulerNativeCursorResult map
            (onReturned result finalState finalCoherent))
  | .forkPair frozenHistory pairRoom outputInput advanceInput template next =>
      .forkPair frozenHistory pairRoom outputInput advanceInput template
        (fun configuration =>
          mapSchedulerNativeCursorResult map (next configuration))
  | .forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next =>
      .forkAdvance frozenHistory pairRoom outputInput advanceInput template
        forkOutput (fun configuration =>
          mapSchedulerNativeCursorResult map (next configuration))
  | .returned result => .returned (map result)
  | .failed reason => .failed reason

@[simp] theorem map_scheduler_native_cursor_returned
    {globalOracleCalls : Nat} {Input Output : Type u}
    (map : Input → Output) (result : Input) :
    mapSchedulerNativeCursorResult map
      (.returned result : SchedulerNativeCursor globalOracleCalls Input) =
        .returned (map result) := by
  rfl

@[simp] theorem map_scheduler_native_cursor_failed
    {globalOracleCalls : Nat} {Input Output : Type u}
    (map : Input → Output) (reason : SchedulerNativeFailure) :
    mapSchedulerNativeCursorResult map
      (.failed reason : SchedulerNativeCursor globalOracleCalls Input) =
        .failed reason := by
  rfl

/-! ## Plain result and exact root runtime data -/

inductive SchedulerNativePlainRomInitialFailure where
  | adversaryRoom
  | adversaryOracleAbort (reason : OracleAbort)
  | adversaryTimeout
  | verifierRoom
  | verifierOracleAbort (reason : OracleAbort)
  | verifierTimeout
  deriving DecidableEq, Repr

/-- Root runtime data built only inside the actual prover/verifier scheduler
callbacks.  It is plain data: the invariant relating these fields to the
machine trace is proved separately rather than stored as a field. -/
structure SchedulerNativePlainRomRootRuntime
    (TapeIdentity Statement Proof Payload : Type u) where
  tapeIdentity : TapeIdentity
  adversaryValue :
    CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  proverFinalOracle : OracleState
  verifierFinalOracle : OracleState
  verifierFinalState : FutureFreeVerifierState

def SchedulerNativePlainRomRootRuntime.node
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : ConcreteRestorationNode Statement Proof Payload where
  parentRequest := none
  adversaryValue := runtime.adversaryValue
  proverEntryOracle := emptyOracle
  proverFinalOracle := runtime.proverFinalOracle
  verifierEntryOracle := runtime.proverFinalOracle
  verifierFinalOracle := runtime.verifierFinalOracle
  verifierEntryState := initialFutureFreeVerifierState
    (FixedBindings.ofContext runtime.adversaryValue.rawMessages.context)
  verifierFinalState := runtime.verifierFinalState

/-- Protocol result retained when the native scheduler reaches a terminal
cursor.  Scheduler resource failures remain the separate existing
`SchedulerNativeTerminal.failed` branch. -/
inductive SchedulerNativePlainRomResult
    (TapeIdentity Statement Proof Payload Result : Type u) where
  | initialFailure (reason : SchedulerNativePlainRomInitialFailure)
  | completed
      (root : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
        Payload)
      (clientRun : ConcreteRestorationClientRun Statement Proof Payload Result)

/-- Convenience constructor for the root runtime delivered by the two nested
callbacks. -/
def operationalRootRuntime
    {TapeIdentity Statement Proof Payload : Type u}
    (tapeIdentity : TapeIdentity)
    (adversaryValue :
      CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
    (proverFinalOracle verifierFinalOracle : OracleState)
    (verifierFinalState : FutureFreeVerifierState) :
    SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof Payload where
  tapeIdentity := tapeIdentity
  adversaryValue := adversaryValue
  proverFinalOracle := proverFinalOracle
  verifierFinalOracle := verifierFinalOracle
  verifierFinalState := verifierFinalState

@[simp] theorem operational_root_node_has_exact_boundaries
    {TapeIdentity Statement Proof Payload : Type u}
    (tapeIdentity : TapeIdentity)
    (adversaryValue :
      CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
    (proverFinalOracle verifierFinalOracle : OracleState)
    (verifierFinalState : FutureFreeVerifierState) :
    let root := (operationalRootRuntime tapeIdentity adversaryValue
      proverFinalOracle verifierFinalOracle verifierFinalState).node
    root.parentRequest = none ∧
      root.proverEntryOracle = emptyOracle ∧
      root.proverFinalOracle = proverFinalOracle ∧
      root.verifierEntryOracle = proverFinalOracle ∧
      root.verifierFinalOracle = verifierFinalOracle ∧
      root.verifierFinalState = verifierFinalState := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! These predicates are proof hooks, not runtime fields.  The root hook is
the exact history/fixed-instance invariant expected from the raw verifier
driver.  The child hook says its entry state is the singleton restoration of
an actual indexed parent transition; the request cannot supply that state. -/

def SchedulerNativePlainRomRootInvariant
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : Prop :=
  FutureFreeRunInvariant
    (FixedBindings.ofContext runtime.adversaryValue.rawMessages.context)
    runtime.verifierFinalState

def ChildNodeIsExactIndexedRestoration
    {Statement Proof Payload : Type u}
    (parent child : ConcreteRestorationNode Statement Proof Payload) : Prop :=
  ∃ request transition,
    child.parentRequest = some request ∧
      verifierTransitionAt? parent request.verifierTransitionIndex =
        some transition ∧
      squeezePairInputsOfTransition transition ≠ none ∧
      child.verifierEntryState = restoreIndexedTransition transition

def SchedulerNativeNodeStoreInvariant
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Prop :=
  accumulator.node? 0 = some runtime.node ∧
    ∀ child ∈ accumulator.nodes, ∀ request,
      child.parentRequest = some request →
        ∃ parent transition,
          accumulator.node? request.nodeId = some parent ∧
            verifierTransitionAt? parent
                request.verifierTransitionIndex = some transition ∧
            squeezePairInputsOfTransition transition ≠ none ∧
            child.verifierEntryState = restoreIndexedTransition transition

theorem exact_indexed_child_entry_is_nonempty
    {Statement Proof Payload : Type u}
    {parent child : ConcreteRestorationNode Statement Proof Payload}
    (exact : ChildNodeIsExactIndexedRestoration parent child) :
    child.verifierEntryState.seen ≠ [] := by
  rcases exact with ⟨request, transition, _parentRequest, _indexed, _squeeze,
    entry⟩
  rw [entry]
  exact restore_indexed_transition_is_nonempty transition

/-! ## One fixed cursor from literal start to the restoration client -/

/-- The two root machine limits must fit the shared strict global call cap.
Restoration stages check their own configured limit before installing a
machine node. -/
structure SchedulerNativeRootLimitBounds
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (globalOracleCalls : Nat) where
  adversary : machine.adversaryLimits.totalCalls ≤ globalOracleCalls
  verifier : machine.verifierLimits.totalCalls ≤ globalOracleCalls

def SameHiddenStartInvariant
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)) : Prop :=
  startProgram = machine.blackBox.start hidden machine.observation

@[simp] theorem literal_start_has_same_hidden_start_invariant
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) :
    SameHiddenStartInvariant machine hidden
      (machine.blackBox.start hidden machine.observation) := by
  rfl

/-- The actual plain-ROM cursor.  Both room tests are executable and become
ordinary protocol failures; callers cannot assume successful initial runs.
The only program restarted by the client is the same literal
`blackBox.start hidden observation` installed at the root. -/
def schedulerNativePlainRomCursor
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result) :
    SchedulerNativeCursor globalOracleCalls
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result) := by
  classical
  let Final := SchedulerNativePlainRomResult TapeIdentity Statement Proof
    Payload Result
  let startProgram := machine.blackBox.start hidden machine.observation
  exact if adversaryRoom : StageHasOracleRoom machine.adversaryLimits
      emptyOracle machine.adversaryFuel then
    .machine machine.adversaryLimits limitBounds.adversary .adversary
      emptyOracle
      (schedulerStageProgram Final
        (totalizeOracleMachine machine.adversaryFuel startProgram))
      machine.adversaryFuel empty_oracle_history_total_coherent
      (fun adversaryStage proverFinalOracle proverCoherent =>
        match adversaryStage with
        | .completed adversaryResult =>
            match adversaryResult with
            | .error (.oracleAbort reason) =>
                .returned (.initialFailure (.adversaryOracleAbort reason))
            | .error .timeout =>
                .returned (.initialFailure .adversaryTimeout)
            | .ok adversaryValue =>
                if verifierRoom : StageHasOracleRoom machine.verifierLimits
                    proverFinalOracle machine.verifierFuel then
                  .machine machine.verifierLimits limitBounds.verifier
                    .verifier proverFinalOracle
                    (schedulerStageProgram Final
                      (totalizeOracleMachine machine.verifierFuel
                        (initialRawFutureFreeProgram machine.environment
                          adversaryValue.rawMessages machine.driverFuel)))
                    machine.verifierFuel proverCoherent
                    (fun verifierStage verifierFinalOracle _verifierCoherent =>
                      match verifierStage with
                      | .completed verifierResult =>
                          match verifierResult with
                          | .error (.oracleAbort reason) =>
                              .returned (.initialFailure
                                (.verifierOracleAbort reason))
                          | .error .timeout =>
                              .returned (.initialFailure .verifierTimeout)
                          | .ok verifierFinalState =>
                              let rootRuntime := operationalRootRuntime
                                (machine.tapeIdentity hidden) adversaryValue
                                proverFinalOracle verifierFinalOracle
                                verifierFinalState
                              mapSchedulerNativeCursorResult
                                (fun clientRun => .completed rootRuntime
                                  clientRun)
                                (startConcreteRestorationClientFromRoot
                                  (globalOracleCalls := globalOracleCalls)
                                  startProgram machine.environment
                                  rootRuntime.node
                                  restorationConfiguration restorationFuel
                                  client))
                else
                  .returned (.initialFailure .verifierRoom))
  else
    .returned (.initialFailure .adversaryRoom)

@[simp] theorem scheduler_native_plain_rom_uses_literal_same_hidden_start
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (_limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (_restorationConfiguration : ConcreteRestorationConfiguration)
    (_restorationFuel : Nat)
    (_client : ConcreteRestorationClient Result) :
    machine.blackBox.start hidden machine.observation =
      (closeSameTapeStart machine.blackBox hidden
        (machine.tapeIdentity hidden)).start machine.observation := by
  rfl

/-! ## Fixed master-tape experiment -/

def runSchedulerNativePlainRom
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls exposures : Nat}
    (transitionFuel : Nat)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (masterTape : FreshAnswerTape Digest256 exposures) :
    SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result) :=
  runSchedulerNative transitionFuel exposures
    (schedulerNativePlainRomCursor machine hidden limitBounds
      restorationConfiguration restorationFuel client) masterTape

theorem scheduler_native_plain_rom_trace_has_fixed_length
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls exposures : Nat}
    (transitionFuel : Nat)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (masterTape : FreshAnswerTape Digest256 exposures) :
    (runSchedulerNativePlainRom transitionFuel machine hidden limitBounds
      restorationConfiguration restorationFuel client masterTape).trace.length =
        exposures := by
  exact run_scheduler_native_trace_length_exact transitionFuel exposures
    (schedulerNativePlainRomCursor machine hidden limitBounds
      restorationConfiguration restorationFuel client) masterTape

theorem scheduler_native_plain_rom_trace_answers_are_master_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls exposures : Nat}
    (transitionFuel : Nat)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (masterTape : FreshAnswerTape Digest256 exposures) :
    (runSchedulerNativePlainRom transitionFuel machine hidden limitBounds
      restorationConfiguration restorationFuel client masterTape).trace.map
        UnifiedExposureRecord.answer = freshAnswerTapeToList masterTape := by
  exact run_scheduler_native_answers_are_exact_tape transitionFuel exposures
    (schedulerNativePlainRomCursor machine hidden limitBounds
      restorationConfiguration restorationFuel client) masterTape

#print axioms map_scheduler_native_cursor_returned
#print axioms operational_root_node_has_exact_boundaries
#print axioms exact_indexed_child_entry_is_nonempty
#print axioms literal_start_has_same_hidden_start_invariant
#print axioms scheduler_native_plain_rom_uses_literal_same_hidden_start
#print axioms scheduler_native_plain_rom_trace_has_fixed_length
#print axioms scheduler_native_plain_rom_trace_answers_are_master_tape

end

end AspisK1.V7Tag73SchedulerNativePlainRomExperiment
