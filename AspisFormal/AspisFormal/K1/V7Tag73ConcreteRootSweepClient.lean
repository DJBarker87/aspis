import AspisFormal.K1.V7Tag73UniqueRestorationRequests
import AspisFormal.K1.V7Tag73SchedulerNativeSafety

/-!
# A finite root-transition sweep client for Tag-73 extraction

The deployed future-free verifier records a bounded list of transitions, but
the exact indices of squeeze transitions depend on the accepted execution.
The extractor must not guess a transcript role from a raw SHA coordinate:
an adversary may have queried that coordinate first.  Instead, the concrete
dispatcher accepts a verifier-transition index, derives the corresponding
pair of squeeze inputs from the stored snapshot, and replays the same-tape
prover to the first occurrence of either input.

This file constructs the finite client needed to exercise that dispatcher.
One sweep requests every root transition in a fixed half-open interval.
Nonexistent and non-squeeze indices fail closed and the client continues;
genuine squeeze indices create the controlled restoration nodes needed by the
K1.3--K1.5 probability arguments.  Repeated sweeps are supported because
ordinary extraction needs multiple independent responses at the same root
challenge and root nodes are immutable.

The construction is reply-insensitive.  Its exact request count and
replay-base-safe discipline are proved structurally, with no success,
probability, transcript-role, or extraction premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ConcreteRootSweepClient

open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73UniqueRestorationRequests
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeSafety
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73InteractiveAncestor

universe u

/-- Prepend requests for the root transitions
`start, start + 1, ..., start + count - 1` to an arbitrary client tail.
Every reply takes the same continuation. -/
def prependRootTransitionSweep {Result : Type u} (start : Nat) :
    (count : Nat) → ConcreteRestorationClient Result →
      ConcreteRestorationClient Result
  | 0, tail => tail
  | count + 1, tail =>
      .restore
        { nodeId := 0, verifierTransitionIndex := start }
        (fun _reply => prependRootTransitionSweep (start + 1) count tail)

@[simp] theorem prependRootTransitionSweep_zero
    {Result : Type u} (start : Nat)
    (tail : ConcreteRestorationClient Result) :
    prependRootTransitionSweep start 0 tail = tail := by
  rfl

@[simp] theorem prependRootTransitionSweep_succ
    {Result : Type u} (start count : Nat)
    (tail : ConcreteRestorationClient Result) :
    prependRootTransitionSweep start (count + 1) tail =
      .restore { nodeId := 0, verifierTransitionIndex := start }
        (fun _reply => prependRootTransitionSweep (start + 1) count tail) := by
  rfl

/-- Repeat a complete root interval sweep.  Each round starts again at index
zero, which is valid because every request is based on the immutable root. -/
def repeatRootTransitionSweep {Result : Type u} (transitionCount : Nat) :
    (rounds : Nat) → ConcreteRestorationClient Result →
      ConcreteRestorationClient Result
  | 0, tail => tail
  | rounds + 1, tail =>
      prependRootTransitionSweep 0 transitionCount
        (repeatRootTransitionSweep transitionCount rounds tail)

@[simp] theorem repeatRootTransitionSweep_zero
    {Result : Type u} (transitionCount : Nat)
    (tail : ConcreteRestorationClient Result) :
    repeatRootTransitionSweep transitionCount 0 tail = tail := by
  rfl

@[simp] theorem repeatRootTransitionSweep_succ
    {Result : Type u} (transitionCount rounds : Nat)
    (tail : ConcreteRestorationClient Result) :
    repeatRootTransitionSweep transitionCount (rounds + 1) tail =
      prependRootTransitionSweep 0 transitionCount
        (repeatRootTransitionSweep transitionCount rounds tail) := by
  rfl

/-- A reply-branch-independent certificate that a client issues exactly
`count` requests and then returns the named result.  This is a static property
of the extractor program, not a claim that any restoration request succeeds. -/
inductive ExactRequestCount {Result : Type u} (result : Result) :
    Nat → ConcreteRestorationClient Result → Prop where
  | pure : ExactRequestCount result 0 (.pure result)
  | restore (request : ConcreteRestorationRequest)
      (next : ConcreteRestorationReply → ConcreteRestorationClient Result)
      {count : Nat}
      (tails : ∀ reply, ExactRequestCount result count (next reply)) :
      ExactRequestCount result (count + 1) (.restore request next)

theorem prepend_root_transition_sweep_exact_request_count
    {Result : Type u} (result : Result) (start count : Nat) :
    ExactRequestCount result count
      (prependRootTransitionSweep start count (.pure result)) := by
  induction count generalizing start with
  | zero => exact .pure
  | succ count ih =>
      apply ExactRequestCount.restore
      intro reply
      exact ih (start + 1)

/-- Prepending a sweep adds exactly its interval length to any already
certified reply-insensitive client tail. -/
theorem prepend_root_transition_sweep_adds_exact_request_count
    {Result : Type u} {result : Result} {tailCount : Nat}
    {tail : ConcreteRestorationClient Result}
    (tailExact : ExactRequestCount result tailCount tail)
    (start count : Nat) :
    ExactRequestCount result (count + tailCount)
      (prependRootTransitionSweep start count tail) := by
  induction count generalizing start with
  | zero => simpa using tailExact
  | succ count ih =>
      have tails : ∀ (_reply : ConcreteRestorationReply),
          ExactRequestCount result (count + tailCount)
            (prependRootTransitionSweep (start + 1) count tail) := by
        intro reply
        exact ih (start + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ExactRequestCount.restore
          { nodeId := 0, verifierTransitionIndex := start }
          (fun _reply => prependRootTransitionSweep (start + 1) count tail)
          tails)

theorem repeat_root_transition_sweep_exact_request_count
    {Result : Type u} (result : Result) (transitionCount rounds : Nat) :
    ExactRequestCount result (rounds * transitionCount)
      (repeatRootTransitionSweep transitionCount rounds (.pure result)) := by
  induction rounds with
  | zero => simpa using (ExactRequestCount.pure (result := result))
  | succ rounds ih =>
      simpa [Nat.succ_mul, Nat.add_comm] using
        prepend_root_transition_sweep_adds_exact_request_count ih 0
          transitionCount

/-- A root sweep satisfies the operational scheduling rule regardless of its
tail: every generated request names node zero. -/
theorem prepend_root_transition_sweep_replay_base_safe
    {Result : Type u} (start count : Nat)
    (tail : ConcreteRestorationClient Result)
    (tailSafe : ReplayBaseSafeConcreteClient tail) :
    ReplayBaseSafeConcreteClient
      (prependRootTransitionSweep start count tail) := by
  induction count generalizing start with
  | zero => simpa using tailSafe
  | succ count ih =>
      apply ReplayBaseSafeConcreteClient.restore
      · exact root_restoration_request_is_replay_base_safe start
      · intro reply
        exact ih (start + 1)

theorem repeat_root_transition_sweep_replay_base_safe
    {Result : Type u} (transitionCount rounds : Nat)
    (tail : ConcreteRestorationClient Result)
    (tailSafe : ReplayBaseSafeConcreteClient tail) :
    ReplayBaseSafeConcreteClient
      (repeatRootTransitionSweep transitionCount rounds tail) := by
  induction rounds with
  | zero => simpa using tailSafe
  | succ rounds ih =>
      exact prepend_root_transition_sweep_replay_base_safe 0 transitionCount
        _ ih

/-- The production-shaped sweep client: inspect the complete deployed
1511-transition cap for each requested extraction round, then return the fixed
accumulator extractor supplied independently of the hidden tape. -/
def deployedRootSweepClient {Result : Type u} (rounds : Nat)
    (result : Result) : ConcreteRestorationClient Result :=
  repeatRootTransitionSweep 1511 rounds (.pure result)

theorem deployed_root_sweep_client_exact_request_count
    {Result : Type u} (rounds : Nat) (result : Result) :
    ExactRequestCount result (rounds * 1511)
      (deployedRootSweepClient rounds result) := by
  exact repeat_root_transition_sweep_exact_request_count result 1511 rounds

theorem deployed_root_sweep_client_replay_base_safe
    {Result : Type u} (rounds : Nat) (result : Result) :
    ReplayBaseSafeConcreteClient (deployedRootSweepClient rounds result) := by
  apply repeat_root_transition_sweep_replay_base_safe
  exact ReplayBaseSafeConcreteClient.pure result

/-! ## Exact fuel closure -/

/-- The real one-request dispatcher preserves any terminal property already
proved for every adaptive reply continuation.  This theorem unfolds the
actual preparation, fork, replay and verifier-suffix dispatcher; it does not
replace it by an abstract handler. -/
theorem dispatch_one_concrete_restoration_preserves_all_returned
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
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (P : ConcreteRestorationClientRun Statement Proof Payload Result → Prop)
    (continuations : ∀ reply nextAccumulator,
      SchedulerNativeCursorAllReturned P (resume reply nextAccumulator)) :
    SchedulerNativeCursorAllReturned P
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  classical
  have failureSafe : ∀
      (failureRequest : ConcreteRestorationRequest)
      (reason : ConcreteRestorationFailure)
      (nextAccumulator :
        ConcreteRestorationAccumulator Statement Proof Payload),
      SchedulerNativeCursorAllReturned P
        (resume (.failed reason)
          (nextAccumulator.addFailure failureRequest reason)) := by
    intro failureRequest reason nextAccumulator
    exact continuations _ _
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
      exact failureSafe request reason _
  | ready prepared =>
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
      unfold dispatchPreparedRestoration
      by_cases prefixCoherent :
          HistoryTotalCoherent prepared.programmingBase
      next =>
        simp only [prefixCoherent, if_pos]
        by_cases globalLimit :
            configuration.oracleLimits.totalCalls ≤ globalOracleCalls
        next =>
          simp only [globalLimit, if_pos]
          by_cases pairRoom : prepared.programmingBase.history.length + 2 ≤
              globalOracleCalls
          next =>
            simp only [pairRoom, if_pos]
            intro forkConfiguration
            simp only
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                forkConfiguration.forkOutput forkConfiguration.forkAdvance with
            | failed reason inserted =>
                simp only [programmed]
                exact failureSafe prepared.request reason _
            | ready afterBoth =>
                simp only [programmed]
                by_cases afterCoherent : HistoryTotalCoherent afterBoth
                next =>
                  simp only [afterCoherent, if_pos]
                  by_cases proverRoom : StageHasOracleRoom
                      configuration.oracleLimits afterBoth
                      configuration.proverReplayFuel
                  next =>
                    simp only [proverRoom, if_pos]
                    intro proverStage proverFinalOracle proverCoherent
                    cases proverStage with
                    | completed proverResult =>
                        simp only
                        cases proverResult with
                        | error failure =>
                            cases failure with
                            | oracleAbort reason =>
                                exact failureSafe prepared.request
                                  (.proverReplayAbort reason) _
                            | timeout =>
                                exact failureSafe prepared.request
                                  .proverReplayTimeout _
                        | ok adversaryValue =>
                            simp only
                            by_cases bindingMismatch :
                                FixedBindings.ofContext
                                    adversaryValue.rawMessages.context ≠
                                  prepared.restoredState.current.bindings
                            next =>
                              rw [dif_pos bindingMismatch]
                              exact failureSafe prepared.request
                                .restoredBindingMismatch _
                            next =>
                              rw [dif_neg bindingMismatch]
                              by_cases verifierRoom : StageHasOracleRoom
                                  configuration.oracleLimits proverFinalOracle
                                  configuration.verifierFuel
                              next =>
                                simp only [verifierRoom, if_pos]
                                intro verifierStage verifierFinalOracle
                                  verifierCoherent
                                cases verifierStage with
                                | completed verifierResult =>
                                    simp only
                                    cases verifierResult with
                                    | error failure =>
                                        cases failure with
                                        | oracleAbort reason =>
                                            exact failureSafe prepared.request
                                              (.verifierSuffixAbort reason) _
                                        | timeout =>
                                            exact failureSafe prepared.request
                                              .verifierSuffixTimeout _
                                    | ok verifierFinalState =>
                                        exact continuations (.added _) _
                              next =>
                                simp only [verifierRoom, if_neg]
                                exact failureSafe prepared.request
                                  .verifierSuffixRoom _
                  next =>
                    simp only [proverRoom, if_neg]
                    exact failureSafe prepared.request .proverReplayRoom _
                next =>
                  simp only [afterCoherent, if_neg]
                  exact failureSafe prepared.request
                    .incoherentProgrammedOracle _
          next =>
            simp only [pairRoom, if_neg]
            exact failureSafe prepared.request .pairExposureLimit _
        next =>
          simp only [globalLimit, if_neg]
          exact failureSafe prepared.request .globalLimitTooSmall _
      next =>
        simp only [prefixCoherent, if_neg]
        exact failureSafe prepared.request .incoherentPrefixOracle _

/-- A structurally certified client cannot reach the interpreter's
`restorationFuelExhausted` terminal when its exact request count fits in the
supplied fuel.  This closes the previously external `clientReturned` fact for
all reply-insensitive finite clients, including the deployed root sweep. -/
theorem exact_request_count_prevents_fuel_exhaustion
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (fuel count : Nat)
    (client : ConcreteRestorationClient Result)
    (result : Result)
    (exactCount : ExactRequestCount result count client)
    (fuelEnough : count ≤ fuel) :
    SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload Result =>
        run.halt = .returned result)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration fuel client) := by
  let P := fun run : ConcreteRestorationClientRun Statement Proof Payload
      Result => run.halt = .returned result
  let motive := fun (remainingFuel : Nat)
      (_accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      ∀ residualCount,
        ExactRequestCount result residualCount residualClient →
        residualCount ≤ remainingFuel →
        SchedulerNativeCursorAllReturned P cursor
  have induction :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration fuel client motive
      (by
        intro remainingFuel accumulator terminalResult residualCount certified
          enough
        cases certified
        rfl)
      (by
        intro accumulator request next residualCount certified enough
        cases certified with
        | restore request next tails => omega)
      (by
        intro remainingFuel accumulator request next resume continuations
          residualCount certified enough
        cases certified with
        | restore certifiedRequest certifiedNext tails =>
            apply dispatch_one_concrete_restoration_preserves_all_returned
              startProgram environment configuration accumulator request resume
              P
            intro reply nextAccumulator
            exact continuations reply nextAccumulator _ (tails reply) (by omega))
  exact induction count exactCount fuelEnough

/-- Production specialization: `rounds * 1511` restoration fuel is sufficient
for the complete deployed root-transition sweep to return its fixed result on
every scheduler branch. -/
theorem deployed_root_sweep_client_returns
    {Statement Proof Payload Result : Type*}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (rounds : Nat) (result : Result) :
    SchedulerNativeCursorAllReturned
      (fun run : ConcreteRestorationClientRun Statement Proof Payload Result =>
        run.halt = .returned result)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration (rounds * 1511)
        (deployedRootSweepClient rounds result)) := by
  apply exact_request_count_prevents_fuel_exhaustion
    startProgram environment root configuration (rounds * 1511)
    (rounds * 1511) (deployedRootSweepClient rounds result) result
  · exact deployed_root_sweep_client_exact_request_count rounds result
  · exact Nat.le_refl _

#print axioms prepend_root_transition_sweep_exact_request_count
#print axioms prepend_root_transition_sweep_adds_exact_request_count
#print axioms repeat_root_transition_sweep_exact_request_count
#print axioms prepend_root_transition_sweep_replay_base_safe
#print axioms repeat_root_transition_sweep_replay_base_safe
#print axioms deployed_root_sweep_client_exact_request_count
#print axioms deployed_root_sweep_client_replay_base_safe
#print axioms dispatch_one_concrete_restoration_preserves_all_returned
#print axioms exact_request_count_prevents_fuel_exhaustion
#print axioms deployed_root_sweep_client_returns

end AspisK1.V7Tag73ConcreteRootSweepClient
