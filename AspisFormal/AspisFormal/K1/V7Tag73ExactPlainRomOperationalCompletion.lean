import AspisFormal.K1.V7Tag73ExactCompilerClientCaps
import AspisFormal.K1.V7Tag73SchedulerResultMapSemantics
import AspisFormal.K1.V7Tag73SchedulerCompletionCore

/-!
# Operational completion of the exact Tag-73 plain-ROM scheduler

This module proves the resource direction that is deliberately absent from
`ExactPlainRomOperationalBounds`.  Passing a stage's executable
`StageHasOracleRoom` guard makes its totalized oracle program scheduler-safe:
it cannot explicitly abort, exhaust its query fuel, or hit an oracle counter
limit.  A list with at least the stage fuel many coordinates therefore contains
enough fresh answers for every possible adaptive path.

The second half composes those facts through the literal concrete restoration
dispatcher.  A request consumes at most two fork coordinates, `Q` complete
same-tape replay coordinates, and 1511 verifier coordinates.  Synchronous
prefix replay is not sampled from the master tape and is retained separately
in the concrete accumulator's runtime charges.

No acceptance, witness, target-event inclusion, controller equality, or
compiler conclusion is a premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactPlainRomOperationalCompletion

set_option maxRecDepth 8192

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerResultMapSemantics
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactCompilerClientCaps
open AspisK1.V7Tag73SchedulerCompletionCore

noncomputable section

universe u v

/- The generic machine/fork completion lemmas formerly developed inline are
now isolated in `V7Tag73TotalizedStageCompletion` and
`V7Tag73SchedulerCompletionCore`.  This retained draft is commented while the
dispatcher-specific composition below migrates to their checked API.

/-! ## A totalized stage cannot produce a native machine failure -/

/-- Proof-rich classification of the normalizer applied to a mapped,
totalized program.  The request constructor exposes the literal residual
original program, a strict decrease in fuel, and the room invariant before the
pending query. -/
inductive MappedTotalizedSeekCertificate
    {Original : Type u} {Mapped : Type v}
    (limits : OracleLimits) (actor : QueryActor)
    (map : Except TotalizedMachineFailure Original → Mapped) :
    (fuel : Nat) → (state : OracleState) →
      (program : OracleMachine Original) →
      (coherent : HistoryTotalCoherent state) →
      SeekNextFreshResult Mapped limits → Prop where
  | returned
      (fuel : Nat) (state : OracleState) (program : OracleMachine Original)
      (coherent : HistoryTotalCoherent state)
      (value : Except TotalizedMachineFailure Original)
      (finalState : OracleState) (steps : Nat) :
      MappedTotalizedSeekCertificate limits actor map fuel state program
        coherent (.returned (map value) finalState steps)
  | request
      (fuel : Nat) (state : OracleState) (program : OracleMachine Original)
      (coherent : HistoryTotalCoherent state)
      (requestState : OracleState) (input : ShaInput)
      (nextOriginal : ShaOutput → OracleMachine Original)
      (remainingFuel steps : Nat)
      (requestCoherent : HistoryTotalCoherent requestState)
      (totalRoom : requestState.totalCalls < limits.totalCalls)
      (freshRoom : requestState.freshCalls < limits.freshCalls)
      (missing : lookupEntry requestState input = none)
      (remainingLt : remainingFuel < fuel)
      (stageRoom : StageHasOracleRoom limits requestState (remainingFuel + 1)) :
      MappedTotalizedSeekCertificate limits actor map fuel state program coherent
        (.request requestState input
          (fun answer => mapOracleMachineResult map
            (totalizeOracleMachine remainingFuel (nextOriginal answer)))
          remainingFuel steps requestCoherent totalRoom freshRoom missing)

/-- Executing cached queries preserves the certificate while incrementing only
the completed-step counter. -/
theorem mapped_totalized_seek_certificate_add_completed
    {Original : Type u} {Mapped : Type v}
    (limits : OracleLimits) (actor : QueryActor)
    (map : Except TotalizedMachineFailure Original → Mapped)
    (outerFuel : Nat) (outerState : OracleState)
    (outerProgram : OracleMachine Original)
    (outerCoherent : HistoryTotalCoherent outerState)
    (innerFuel : Nat) (innerState : OracleState)
    (innerProgram : OracleMachine Original)
    (innerCoherent : HistoryTotalCoherent innerState)
    (result : SeekNextFreshResult Mapped limits)
    (innerLt : innerFuel < outerFuel)
    (certificate : MappedTotalizedSeekCertificate limits actor map innerFuel
      innerState innerProgram innerCoherent result) :
    MappedTotalizedSeekCertificate limits actor map outerFuel outerState
      outerProgram outerCoherent result.addCompletedQuery := by
  cases certificate with
  | returned value finalState steps =>
      exact .returned outerFuel outerState outerProgram outerCoherent value
        finalState (steps + 1)
  | request requestState input nextOriginal
      remainingFuel steps requestCoherent totalRoom freshRoom missing remainingLt
      stageRoom =>
      exact .request outerFuel outerState outerProgram outerCoherent requestState
        input nextOriginal
        remainingFuel (steps + 1) requestCoherent totalRoom freshRoom missing
        (remainingLt.trans innerLt) stageRoom

/-- The exact mapped totalization used by scheduler stages is either already a
normal return or a fresh request whose residual is again the same mapped
totalization.  Native abort/resource/fuel constructors are impossible. -/
theorem seek_next_fresh_mapped_totalized_certificate
    {Original : Type u} {Mapped : Type v}
    (limits : OracleLimits) (actor : QueryActor)
    (map : Except TotalizedMachineFailure Original → Mapped) :
    ∀ (fuel : Nat) (state : OracleState)
      (program : OracleMachine Original)
      (coherent : HistoryTotalCoherent state),
      StageHasOracleRoom limits state fuel →
      MappedTotalizedSeekCertificate limits actor map fuel state program coherent
        (seekNextFresh limits actor fuel state
          (mapOracleMachineResult map (totalizeOracleMachine fuel program))
          coherent) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program coherent room
      cases program with
      | pure value =>
          exact .returned 0 state (.pure value) coherent (.ok value) state 0
      | abort reason =>
          exact .returned 0 state (.abort reason) coherent
            (.error (.oracleAbort reason)) state 0
      | query input next =>
          exact .returned 0 state (.query input next) coherent
            (.error .timeout) state 0
  | succ fuel ih =>
      intro state program coherent room
      cases program with
      | pure value =>
          exact .returned (fuel + 1) state (.pure value) coherent (.ok value)
            state 0
      | abort reason =>
          exact .returned (fuel + 1) state (.abort reason) coherent
            (.error (.oracleAbort reason)) state 0
      | query input next =>
          have totalNotBlocked : ¬ state.totalCalls ≥ limits.totalCalls := by
            unfold StageHasOracleRoom at room
            omega
          simp only [totalizeOracleMachine, mapOracleMachineResult,
            seekNextFresh, totalNotBlocked, if_false]
          cases found : lookupEntry state input with
          | some entry =>
              simp only [found]
              have cachedRoom : StageHasOracleRoom limits
                  (cachedQueryState actor state input entry) fuel := by
                unfold StageHasOracleRoom at room ⊢
                simp [cachedQueryState]
                omega
              have tail := ih (cachedQueryState actor state input entry)
                (next entry.output)
                (cached_query_state_preserves_history_total_coherent actor state
                  input entry coherent) cachedRoom
              exact mapped_totalized_seek_certificate_add_completed limits actor
                map (fuel + 1) state (.query input next) coherent fuel
                (cachedQueryState actor state input entry) (next entry.output)
                (cached_query_state_preserves_history_total_coherent actor state
                  input entry coherent) _ (by omega) tail
          | none =>
              simp only [found]
              have freshNotBlocked : ¬ state.freshCalls ≥ limits.freshCalls := by
                unfold StageHasOracleRoom at room
                omega
              simp only [freshNotBlocked, if_false]
              exact .request (fuel + 1) state (.query input next) coherent state
                input next fuel 0 coherent (Nat.lt_of_not_ge totalNotBlocked)
                (Nat.lt_of_not_ge freshNotBlocked) found (by omega) room

/-- Supplying at least `fuel` coordinates to a guarded totalized stage always
produces a projected normal return.  Cached calls reduce the needed coordinate
count; the theorem therefore makes no assumption that all calls are fresh. -/
theorem consume_mapped_totalized_stage_returns
    {Original : Type u} {Mapped : Type v}
    (limits : OracleLimits) (actor : QueryActor)
    (map : Except TotalizedMachineFailure Original → Mapped) :
    ∀ (fuel : Nat) (available : List Digest256) (state : OracleState)
      (program : OracleMachine Original)
      (coherent : HistoryTotalCoherent state),
      StageHasOracleRoom limits state fuel →
      fuel ≤ available.length →
      ∃ returned : ProjectedMachinePrefixReturned limits actor fuel state
          (mapOracleMachineResult map (totalizeOracleMachine fuel program))
          available,
        consumeProjectedMachinePrefix limits actor available fuel state
            (mapOracleMachineResult map (totalizeOracleMachine fuel program))
            coherent = .ok returned := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro available state program coherent room enough
      cases fuel with
      | zero =>
          cases program with
          | pure value =>
              refine ⟨?_, rfl⟩
          | abort reason =>
              refine ⟨?_, rfl⟩
          | query input next =>
              refine ⟨?_, rfl⟩
      | succ predecessor =>
          have certificate := seek_next_fresh_mapped_totalized_certificate limits
            actor map (predecessor + 1) state program coherent room
          generalize soughtExact : seekNextFresh limits actor (predecessor + 1)
              state
              (mapOracleMachineResult map
                (totalizeOracleMachine (predecessor + 1) program)) coherent =
                sought at certificate
          cases certificate with
          | returned value finalState steps =>
              unfold consumeProjectedMachinePrefix
              unfold consumeCertifiedProjectedMachinePrefix
              simp only [certifiedSeekNextFresh, soughtExact]
              refine ⟨?_, rfl⟩
          | request requestState input nextOriginal remainingFuel steps
              requestCoherent totalRoom freshRoom missing remainingLt
              requestRoom =>
              cases available with
              | nil => simp at enough
              | cons answer rest =>
                  have afterRoom : StageHasOracleRoom limits
                      (freshQueryState actor requestState input answer)
                      remainingFuel := by
                    unfold StageHasOracleRoom at requestRoom ⊢
                    simp [freshQueryState]
                    omega
                  have restEnough : remainingFuel ≤ rest.length := by
                    simp only [List.length_cons] at enough
                    omega
                  obtain ⟨tail, tailExact⟩ := ih remainingFuel remainingLt rest
                    (freshQueryState actor requestState input answer)
                    (nextOriginal answer)
                    (fresh_query_state_preserves_history_total_coherent actor
                      requestState input answer requestCoherent) afterRoom
                    restEnough
                  unfold consumeProjectedMachinePrefix
                  unfold consumeCertifiedProjectedMachinePrefix
                  simp only [certifiedSeekNextFresh, soughtExact]
                  rw [tailExact]
                  refine ⟨?_, rfl⟩

/-! ## Semantic completion profiles for native cursors -/

/-- A cursor needs at most `normalizationDepth` consecutive no-coordinate
normalizations and at most `exposureCap` master-tape coordinates.  This is a
theorem-device predicate: later theorems construct it for the literal root and
client cursors. -/
def SchedulerNativeCompletesWithin
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel normalizationDepth exposureCap : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result) : Prop :=
  normalizationDepth ≤ transitionFuel ∧
    ∀ currentTransitionFuel,
      normalizationDepth ≤ currentTransitionFuel →
      ∀ answers : List Digest256,
        exposureCap ≤ answers.length →
        ∃ result,
          runSchedulerNativeListTerminalFrom transitionFuel
            currentTransitionFuel cursor answers = .returned result

theorem scheduler_native_returned_completes_within
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (result : Result) :
    SchedulerNativeCompletesWithin transitionFuel 1 0
      (.returned result : SchedulerNativeCursor globalOracleCalls Result) := by
  constructor
  · omega
  intro current currentPositive answers enough
  refine ⟨result, ?_⟩
  cases current with
  | zero => omega
  | succ current =>
      cases answers with
      | nil =>
          simp [runSchedulerNativeListTerminalFrom, terminalAtExposureEnd,
            seekSchedulerNativeExposure]
      | cons answer rest =>
          simp only [runSchedulerNativeListTerminalFrom,
            seekSchedulerNativeExposure]
          exact run_scheduler_native_list_returned_of_positive transitionFuel
            positive result rest

/-- Extra unused coordinates and a stronger normalization budget preserve a
completion profile. -/
theorem scheduler_native_completes_within_mono
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    {oldDepth newDepth oldExposure newExposure : Nat}
    {cursor : SchedulerNativeCursor globalOracleCalls Result}
    (safe : SchedulerNativeCompletesWithin transitionFuel oldDepth oldExposure
      cursor)
    (depthLe : oldDepth ≤ newDepth) (newDepthLe : newDepth ≤ transitionFuel)
    (exposureLe : oldExposure ≤ newExposure) :
    SchedulerNativeCompletesWithin transitionFuel newDepth newExposure cursor := by
  constructor
  · exact newDepthLe
  intro current currentEnough answers answersEnough
  exact safe.2 current (depthLe.trans currentEnough) answers
    (exposureLe.trans answersEnough)

/-- The fresh prefix consumed by a projected normal return is bounded by the
machine's query fuel. -/
theorem projected_machine_prefix_fresh_length_le_fuel
    {Result : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    returned.freshQueries.length ≤ fuel := by
  have coherent : HistoryTotalCoherent state := by
    cases returned.trace <;> assumption
  have runExact := projected_machine_prefix_returned_run_exact limits actor fuel
    state program available returned coherent
  have stepsLe := run_machine_steps_le_fuel
    (controllerFromProjectedFreshAnswers state.history
      (returned.freshQueries.map Prod.snd)) limits actor fuel state program
  rw [runExact] at stepsLe
  exact (projected_fresh_returned_trace_answer_count_le_steps limits actor fuel
    state program returned.freshQueries returned.result returned.finalState
    returned.steps returned.trace).trans stepsLe

/-- One guarded mapped-totalized machine composes with any uniformly bounded
normal-return continuation.  The additional normalization unit is exact: the
machine itself is normalized before its continuation. -/
theorem mapped_totalized_machine_completes_within
    {Original : Type u} {Mapped Result : Type v}
    {globalOracleCalls : Nat}
    (transitionFuel nextDepth nextExposure : Nat)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (state : OracleState)
    (originalProgram : OracleMachine Original) (fuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (map : Except TotalizedMachineFailure Original → Mapped)
    (onReturned : (result : Mapped) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (stageRoom : StageHasOracleRoom limits state fuel)
    (transitionRoom : nextDepth + 1 ≤ transitionFuel)
    (continuations : ∀ result finalState finalCoherent,
      SchedulerNativeCompletesWithin transitionFuel nextDepth nextExposure
        (onReturned result finalState finalCoherent)) :
    SchedulerNativeCompletesWithin transitionFuel (nextDepth + 1)
      (fuel + nextExposure)
      (.machine limits limitBound actor state
        (mapOracleMachineResult map
          (totalizeOracleMachine fuel originalProgram)) fuel coherent
        onReturned) := by
  constructor
  · exact transitionRoom
  intro current currentRoom answers answersRoom
  have positive : 0 < transitionFuel := by omega
  rw [run_scheduler_native_list_machine_factorization transitionFuel limits
    limitBound actor state
    (mapOracleMachineResult map
      (totalizeOracleMachine fuel originalProgram)) fuel coherent onReturned
    positive current answers]
  cases current with
  | zero => omega
  | succ current =>
      unfold terminalAfterProjectedMachinePrefix
        terminalAfterCertifiedProjectedMachinePrefix
      obtain ⟨returned, returnedExact⟩ :=
        consume_mapped_totalized_stage_returns limits actor map fuel answers state
          originalProgram coherent stageRoom (by omega)
      rw [returnedExact]
      have freshBound := projected_machine_prefix_fresh_length_le_fuel limits
        actor fuel state
        (mapOracleMachineResult map
          (totalizeOracleMachine fuel originalProgram)) answers returned
      have remainingRoom : nextExposure ≤ returned.remaining.length := by
        have lengths := congrArg List.length returned.availableExact
        simp only [List.length_append, List.length_map] at lengths
        omega
      have nextCurrentRoom : nextDepth ≤
          machinePrefixContinuationTransitionFuel transitionFuel current
            returned.freshQueries := by
        cases returned.freshQueries with
        | nil =>
            simp [machinePrefixContinuationTransitionFuel]
            omega
        | cons head tail =>
            simp [machinePrefixContinuationTransitionFuel]
            omega
      exact (continuations returned.result returned.finalState
        returned.finalCoherent).2 _ nextCurrentRoom returned.remaining
          remainingRoom

/-- Result-only cursor mapping cannot introduce a native failure or consume an
additional coordinate. -/
theorem scheduler_native_completes_within_map
    {globalOracleCalls : Nat} {Input Output : Type u}
    (transitionFuel depth exposure : Nat)
    (map : Input → Output)
    {cursor : SchedulerNativeCursor globalOracleCalls Input}
    (safe : SchedulerNativeCompletesWithin transitionFuel depth exposure
      cursor) :
    SchedulerNativeCompletesWithin transitionFuel depth exposure
      (mapSchedulerNativeCursorResult map cursor) := by
  constructor
  · exact safe.1
  intro current currentRoom answers answersRoom
  obtain ⟨result, returned⟩ := safe.2 current currentRoom answers answersRoom
  refine ⟨map result, ?_⟩
  rw [run_scheduler_native_list_terminal_from_map, returned]
  rfl

/-- A direct pair fork consumes exactly two adjacent coordinates.  Its own
normalization depth is one; the adaptive continuation starts after an exposure
reset and may use any depth already bounded by `transitionFuel`. -/
theorem scheduler_native_fork_pair_completes_within
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel nextDepth nextExposure : Nat)
    (frozenHistory : List QueryRecord)
    (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (next : AtomicPairReplayConfiguration →
      SchedulerNativeCursor globalOracleCalls Result)
    (positive : 0 < transitionFuel)
    (continuations : ∀ configuration,
      SchedulerNativeCompletesWithin transitionFuel nextDepth nextExposure
        (next configuration)) :
    SchedulerNativeCompletesWithin transitionFuel 1 (2 + nextExposure)
      (.forkPair frozenHistory pairRoom outputInput advanceInput template next) := by
  constructor
  · omega
  intro current currentPositive answers answersRoom
  cases current with
  | zero => omega
  | succ current =>
      cases answers with
      | nil => simp at answersRoom
      | cons forkOutput rest =>
          cases rest with
          | nil => simp at answersRoom
          | cons forkAdvance tail =>
              let scheduled : ScheduledForkCoins :=
                { frozenHistory := frozenHistory
                  outputInput := outputInput
                  advanceInput := advanceInput
                  template := template
                  forkOutput := forkOutput
                  forkAdvance := forkAdvance }
              have tailRoom : nextExposure ≤ tail.length := by
                simp only [List.length_cons] at answersRoom
                omega
              have nextSafe := continuations scheduled.configuration
              obtain ⟨result, returned⟩ := nextSafe.2 transitionFuel nextSafe.1
                tail tailRoom
              refine ⟨result, ?_⟩
              simp only [runSchedulerNativeListTerminalFrom,
                seekSchedulerNativeExposure]
              simpa [scheduled] using returned

-/

/-! ## The literal concrete client fits the unified exposure tape -/

def oneRestorationExposureCap (Q verifierCalls : Nat) : Nat :=
  2 + Q + verifierCalls

/-- Pad one recursive client continuation to the uniform per-request suffix
budget and, when required by a preceding machine, to normalization depth two
or three. -/
theorem client_tail_completion_padded
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel Q verifierCalls remainingFuel : Nat)
    {cursor : SchedulerNativeCursor globalOracleCalls Result}
    (transitionRoom : 3 ≤ transitionFuel)
    (tail : SchedulerNativeCompletesWithin transitionFuel 1
      (remainingFuel * oneRestorationExposureCap Q verifierCalls) cursor) :
    SchedulerNativeCompletesWithin transitionFuel 3
      (Q + verifierCalls +
        remainingFuel * oneRestorationExposureCap Q verifierCalls) cursor := by
  apply scheduler_native_completes_within_mono transitionFuel tail
  · omega
  · omega
  · omega

/-- One executable dispatcher layer consumes at most one fork pair followed by
the complete prover and verifier stage fuels.  Every synchronous failure branch
uses no additional master coordinate and resumes the literal client tail. -/
theorem dispatch_concrete_restoration_completes_within
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (transitionFuel Q verifierCalls remainingFuel : Nat)
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
    (transitionRoom : 3 ≤ transitionFuel)
    (proverFuelBound : configuration.proverReplayFuel ≤ Q)
    (verifierFuelBound : configuration.verifierFuel ≤ verifierCalls)
    (continuations : ∀ reply nextAccumulator,
      SchedulerNativeCompletesWithin transitionFuel 1
        (remainingFuel * oneRestorationExposureCap Q verifierCalls)
        (resume reply nextAccumulator)) :
    SchedulerNativeCompletesWithin transitionFuel 1
      ((remainingFuel + 1) * oneRestorationExposureCap Q verifierCalls)
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  have positive : 0 < transitionFuel := by omega
  have tailPadded : ∀ reply nextAccumulator,
      SchedulerNativeCompletesWithin transitionFuel 3
        (Q + verifierCalls +
          remainingFuel * oneRestorationExposureCap Q verifierCalls)
        (resume reply nextAccumulator) := by
    intro reply nextAccumulator
    exact client_tail_completion_padded transitionFuel Q verifierCalls
      remainingFuel transitionRoom (continuations reply nextAccumulator)
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration,
        preparationExact]
      apply scheduler_native_completes_within_mono transitionFuel
        (continuations (.failed reason)
          ((accumulator.addCharges
            [.prefixReplayQueries prefixSteps, .restart prefixRestarts]).addFailure
              request reason))
      · omega
      · omega
      · rw [Nat.add_mul]
        simp only [one_mul]
        unfold oneRestorationExposureCap
        omega
  | ready prepared =>
      classical
      let prefixRestarts := if prepared.prefixRun.isSome then 1 else 0
      let withPrefix := accumulator.addCharges
        [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
      simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration,
        preparationExact]
      unfold dispatchPreparedRestoration
      by_cases prefixCoherent : HistoryTotalCoherent prepared.programmingBase
      next =>
        rw [dif_pos prefixCoherent]
        by_cases globalLimit :
            configuration.oracleLimits.totalCalls ≤ globalOracleCalls
        next =>
          rw [dif_pos globalLimit]
          by_cases pairRoom : prepared.programmingBase.history.length + 2 ≤
              globalOracleCalls
          next =>
            rw [dif_pos pairRoom]
            apply scheduler_native_completes_within_mono transitionFuel
              (scheduler_native_fork_pair_completes_within transitionFuel 3
                (Q + verifierCalls +
                  remainingFuel * oneRestorationExposureCap Q verifierCalls)
                prepared.programmingBase.history pairRoom prepared.outputInput
                prepared.advanceInput (canonicalForkTemplate configuration) _
                positive ?_)
            · omega
            · omega
            · rw [Nat.add_mul]
              simp only [one_mul]
              unfold oneRestorationExposureCap
              omega
            intro forkConfiguration
            let afterCoordinates := withPrefix.addCharges
              [.forkUniformCoordinates 2]
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                forkConfiguration.forkOutput forkConfiguration.forkAdvance with
            | failed programmingReason inserted =>
                simp only [programmed]
                exact tailPadded (.failed programmingReason)
                  ((afterCoordinates.addCharges
                    [.programmedPoints inserted]).addFailure prepared.request
                      programmingReason)
            | ready afterBoth =>
                simp only [programmed]
                let afterProgramming := afterCoordinates.addCharges
                  [.programmedPoints 2]
                by_cases afterCoherent : HistoryTotalCoherent afterBoth
                next =>
                  rw [dif_pos afterCoherent]
                  by_cases proverRoom : StageHasOracleRoom
                      configuration.oracleLimits afterBoth
                      configuration.proverReplayFuel
                  next =>
                    rw [dif_pos proverRoom]
                    let atProverStart := afterProgramming.addCharges [.restart 1]
                    apply scheduler_native_completes_within_mono transitionFuel
                      (mapped_totalized_machine_completes_within
                        transitionFuel 2
                        (verifierCalls + remainingFuel *
                          oneRestorationExposureCap Q verifierCalls)
                        configuration.oracleLimits globalLimit .extractorReplay
                        afterBoth startProgram configuration.proverReplayFuel
                        afterCoherent
                        (SchedulerStageResult.completed
                          (Final := ConcreteRestorationClientRun Statement Proof
                            Payload Result))
                        (fun proverStage proverFinalOracle proverCoherent =>
                          match proverStage with
                          | .completed proverResult =>
                              let proverQueries :=
                                (historySince afterBoth proverFinalOracle).length
                              let afterProver := atProverStart.addCharges
                                [.completeFromStartQueries proverQueries]
                              match proverResult with
                              | .error (.oracleAbort reason) =>
                                  resume (.failed (.proverReplayAbort reason))
                                    (afterProver.addFailure prepared.request
                                      (.proverReplayAbort reason))
                              | .error .timeout =>
                                  resume (.failed .proverReplayTimeout)
                                    (afterProver.addFailure prepared.request
                                      .proverReplayTimeout)
                              | .ok adversaryValue =>
                                  let rawMessages :=
                                    CheckedRawTag73AdversaryReturnedValue.rawMessages
                                      adversaryValue
                                  if bindingMismatch :
                                      FixedBindings.ofContext rawMessages.context ≠
                                        prepared.restoredState.current.bindings
                                  then
                                    resume (.failed .restoredBindingMismatch)
                                      (afterProver.addFailure prepared.request
                                        .restoredBindingMismatch)
                                  else if verifierRoom : StageHasOracleRoom
                                      configuration.oracleLimits proverFinalOracle
                                      configuration.verifierFuel then
                                    .machine configuration.oracleLimits globalLimit
                                      .verifier proverFinalOracle
                                      (schedulerStageProgram
                                        (ConcreteRestorationClientRun Statement
                                          Proof Payload Result)
                                        (totalizeOracleMachine
                                          configuration.verifierFuel
                                          (driveRawFutureFree environment
                                            rawMessages configuration.driverFuel
                                            prepared.restoredState)))
                                      configuration.verifierFuel proverCoherent
                                      (fun verifierStage verifierFinalOracle
                                          _verifierCoherent =>
                                        match verifierStage with
                                        | .completed verifierResult =>
                                            let verifierQueries :=
                                              (historySince proverFinalOracle
                                                verifierFinalOracle).length
                                            let afterVerifier :=
                                              afterProver.addCharges
                                                [.verifierSuffixQueries
                                                  verifierQueries]
                                            match verifierResult with
                                            | .error (.oracleAbort reason) =>
                                                resume
                                                  (.failed
                                                    (.verifierSuffixAbort reason))
                                                  (afterVerifier.addFailure
                                                    prepared.request
                                                    (.verifierSuffixAbort reason))
                                            | .error .timeout =>
                                                resume
                                                  (.failed .verifierSuffixTimeout)
                                                  (afterVerifier.addFailure
                                                    prepared.request
                                                    .verifierSuffixTimeout)
                                            | .ok verifierFinalState =>
                                                let transitionCount :=
                                                  verifierFinalState.transitions.length
                                                let node :
                                                    ConcreteRestorationNode
                                                      Statement Proof Payload :=
                                                  { parentRequest :=
                                                      some prepared.request
                                                    adversaryValue := adversaryValue
                                                    proverEntryOracle := afterBoth
                                                    proverFinalOracle :=
                                                      proverFinalOracle
                                                    verifierEntryOracle :=
                                                      proverFinalOracle
                                                    verifierFinalOracle :=
                                                      verifierFinalOracle
                                                    verifierEntryState :=
                                                      prepared.restoredState
                                                    verifierFinalState :=
                                                      verifierFinalState }
                                                let charged :=
                                                  afterVerifier.addCharges
                                                    [.verifierTransitions
                                                      transitionCount]
                                                let added := charged.addNode node
                                                resume (.added added.1) added.2)
                                  else
                                    resume (.failed .verifierSuffixRoom)
                                      (afterProver.addFailure prepared.request
                                        .verifierSuffixRoom))
                        proverRoom (by omega) ?_)
                    · omega
                    · omega
                    · omega
                    intro proverStage proverFinalOracle proverCoherent
                    cases proverStage with
                    | completed proverResult =>
                        let proverQueries :=
                          (historySince afterBoth proverFinalOracle).length
                        let afterProver := atProverStart.addCharges
                          [.completeFromStartQueries proverQueries]
                        cases proverResult with
                        | error failure =>
                            cases failure with
                            | oracleAbort reason =>
                                apply scheduler_native_completes_within_mono
                                  transitionFuel
                                  (continuations
                                    (.failed (.proverReplayAbort reason))
                                    (afterProver.addFailure prepared.request
                                      (.proverReplayAbort reason)))
                                · omega
                                · omega
                                · omega
                            | timeout =>
                                apply scheduler_native_completes_within_mono
                                  transitionFuel
                                  (continuations (.failed .proverReplayTimeout)
                                    (afterProver.addFailure prepared.request
                                      .proverReplayTimeout))
                                · omega
                                · omega
                                · omega
                        | ok adversaryValue =>
                            simp only
                            let rawMessages :=
                              CheckedRawTag73AdversaryReturnedValue.rawMessages
                                adversaryValue
                            by_cases bindingMismatch :
                                FixedBindings.ofContext rawMessages.context ≠
                                  prepared.restoredState.current.bindings
                            next =>
                              rw [dif_pos bindingMismatch]
                              apply scheduler_native_completes_within_mono
                                transitionFuel
                                (continuations
                                  (.failed .restoredBindingMismatch)
                                  (afterProver.addFailure prepared.request
                                    .restoredBindingMismatch))
                              · omega
                              · omega
                              · omega
                            next =>
                              rw [dif_neg bindingMismatch]
                              by_cases verifierRoom : StageHasOracleRoom
                                  configuration.oracleLimits proverFinalOracle
                                  configuration.verifierFuel
                              next =>
                                rw [dif_pos verifierRoom]
                                apply scheduler_native_completes_within_mono
                                  transitionFuel
                                  (mapped_totalized_machine_completes_within
                                    transitionFuel 1
                                    (remainingFuel *
                                      oneRestorationExposureCap Q verifierCalls)
                                    configuration.oracleLimits globalLimit
                                    .verifier proverFinalOracle
                                    (driveRawFutureFree environment rawMessages
                                      configuration.driverFuel
                                      prepared.restoredState)
                                    configuration.verifierFuel proverCoherent
                                    (SchedulerStageResult.completed
                                      (Final := ConcreteRestorationClientRun
                                        Statement Proof Payload Result))
                                    (fun verifierStage verifierFinalOracle
                                        _verifierCoherent =>
                                      match verifierStage with
                                      | .completed verifierResult =>
                                          let verifierQueries :=
                                            (historySince proverFinalOracle
                                              verifierFinalOracle).length
                                          let afterVerifier :=
                                            afterProver.addCharges
                                              [.verifierSuffixQueries
                                                verifierQueries]
                                          match verifierResult with
                                          | .error (.oracleAbort reason) =>
                                              resume
                                                (.failed
                                                  (.verifierSuffixAbort reason))
                                                (afterVerifier.addFailure
                                                  prepared.request
                                                  (.verifierSuffixAbort reason))
                                          | .error .timeout =>
                                              resume
                                                (.failed .verifierSuffixTimeout)
                                                (afterVerifier.addFailure
                                                  prepared.request
                                                  .verifierSuffixTimeout)
                                          | .ok verifierFinalState =>
                                              let transitionCount :=
                                                verifierFinalState.transitions.length
                                              let node : ConcreteRestorationNode
                                                  Statement Proof Payload :=
                                                { parentRequest :=
                                                    some prepared.request
                                                  adversaryValue := adversaryValue
                                                  proverEntryOracle := afterBoth
                                                  proverFinalOracle :=
                                                    proverFinalOracle
                                                  verifierEntryOracle :=
                                                    proverFinalOracle
                                                  verifierFinalOracle :=
                                                    verifierFinalOracle
                                                  verifierEntryState :=
                                                    prepared.restoredState
                                                  verifierFinalState :=
                                                    verifierFinalState }
                                              let charged :=
                                                afterVerifier.addCharges
                                                  [.verifierTransitions
                                                    transitionCount]
                                              let added := charged.addNode node
                                              resume (.added added.1) added.2)
                                    verifierRoom (by omega) ?_)
                                · omega
                                · omega
                                · omega
                                intro verifierStage verifierFinalOracle
                                  verifierCoherent
                                cases verifierStage with
                                | completed verifierResult =>
                                    let verifierQueries :=
                                      (historySince proverFinalOracle
                                        verifierFinalOracle).length
                                    let afterVerifier := afterProver.addCharges
                                      [.verifierSuffixQueries verifierQueries]
                                    cases verifierResult with
                                    | error failure =>
                                        cases failure with
                                        | oracleAbort reason =>
                                            exact continuations
                                              (.failed
                                                (.verifierSuffixAbort reason))
                                              (afterVerifier.addFailure
                                                prepared.request
                                                (.verifierSuffixAbort reason))
                                        | timeout =>
                                            exact continuations
                                              (.failed .verifierSuffixTimeout)
                                              (afterVerifier.addFailure
                                                prepared.request
                                                .verifierSuffixTimeout)
                                    | ok verifierFinalState =>
                                        let transitionCount :=
                                          verifierFinalState.transitions.length
                                        let node : ConcreteRestorationNode
                                            Statement Proof Payload :=
                                          { parentRequest := some prepared.request
                                            adversaryValue := adversaryValue
                                            proverEntryOracle := afterBoth
                                            proverFinalOracle := proverFinalOracle
                                            verifierEntryOracle := proverFinalOracle
                                            verifierFinalOracle :=
                                              verifierFinalOracle
                                            verifierEntryState :=
                                              prepared.restoredState
                                            verifierFinalState :=
                                              verifierFinalState }
                                        let charged := afterVerifier.addCharges
                                          [.verifierTransitions transitionCount]
                                        let added := charged.addNode node
                                        exact continuations (.added added.1)
                                          added.2
                              next =>
                                rw [dif_neg verifierRoom]
                                apply scheduler_native_completes_within_mono
                                  transitionFuel
                                  (continuations (.failed .verifierSuffixRoom)
                                    (afterProver.addFailure prepared.request
                                      .verifierSuffixRoom))
                                · omega
                                · omega
                                · omega
                  next =>
                    rw [dif_neg proverRoom]
                    exact tailPadded (.failed .proverReplayRoom)
                      (afterProgramming.addFailure prepared.request
                        .proverReplayRoom)
                next =>
                  rw [dif_neg afterCoherent]
                  exact tailPadded (.failed .incoherentProgrammedOracle)
                    (afterProgramming.addFailure prepared.request
                      .incoherentProgrammedOracle)
          next =>
            rw [dif_neg pairRoom]
            apply scheduler_native_completes_within_mono transitionFuel
              (continuations (.failed .pairExposureLimit)
                (withPrefix.addFailure prepared.request .pairExposureLimit))
            · omega
            · omega
            · rw [Nat.add_mul]
              simp only [one_mul]
              unfold oneRestorationExposureCap
              omega
        next =>
          rw [dif_neg globalLimit]
          apply scheduler_native_completes_within_mono transitionFuel
            (continuations (.failed .globalLimitTooSmall)
              (withPrefix.addFailure prepared.request .globalLimitTooSmall))
          · omega
          · omega
          · rw [Nat.add_mul]
            simp only [one_mul]
            unfold oneRestorationExposureCap
            omega
      next =>
        rw [dif_neg prefixCoherent]
        apply scheduler_native_completes_within_mono transitionFuel
          (continuations (.failed .incoherentPrefixOracle)
            (withPrefix.addFailure prepared.request .incoherentPrefixOracle))
        · omega
        · omega
        · rw [Nat.add_mul]
          simp only [one_mul]
          unfold oneRestorationExposureCap
          omega

/-- Fuel induction over the literal private client interpreter.  The theorem
constructs completion for every adaptive client; it does not assume that a
particular run returned. -/
theorem concrete_restoration_client_completes_within
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (transitionFuel Q verifierCalls : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (transitionRoom : 3 ≤ transitionFuel)
    (proverFuelBound : configuration.proverReplayFuel ≤ Q)
    (verifierFuelBound : configuration.verifierFuel ≤ verifierCalls) :
    SchedulerNativeCompletesWithin transitionFuel 1
      (restorationFuel * oneRestorationExposureCap Q verifierCalls)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration restorationFuel client) := by
  let motive := fun (fuel : Nat)
      (_accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (_residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      SchedulerNativeCompletesWithin transitionFuel 1
        (fuel * oneRestorationExposureCap Q verifierCalls) cursor
  exact start_concrete_restoration_client_from_root_dependent_induction
    (globalOracleCalls := globalOracleCalls) startProgram environment root
    configuration restorationFuel client motive
    (by
      intro fuel accumulator result
      change SchedulerNativeCompletesWithin transitionFuel 1
        (fuel * oneRestorationExposureCap Q verifierCalls)
        (.returned
          ({ halt := .returned result, accumulator := accumulator } :
            ConcreteRestorationClientRun Statement Proof Payload Result))
      exact scheduler_native_completes_within_mono transitionFuel
        (newDepth := 1)
        (newExposure := fuel * oneRestorationExposureCap Q verifierCalls)
        (scheduler_native_returned_completes_within
          (globalOracleCalls := globalOracleCalls) transitionFuel (by omega)
          ({ halt := .returned result, accumulator := accumulator } :
            ConcreteRestorationClientRun Statement Proof Payload Result))
        (by omega) (by omega) (by omega))
    (by
      intro accumulator request next
      change SchedulerNativeCompletesWithin transitionFuel 1
        (0 * oneRestorationExposureCap Q verifierCalls)
        (.returned
          ({ halt := .restorationFuelExhausted
             accumulator := accumulator.addFailure request
               .restorationFuelExhausted } :
            ConcreteRestorationClientRun Statement Proof Payload Result))
      simpa only [Nat.zero_mul] using
        (scheduler_native_returned_completes_within
          (globalOracleCalls := globalOracleCalls) transitionFuel (by omega)
          ({ halt := .restorationFuelExhausted
             accumulator := accumulator.addFailure request
               .restorationFuelExhausted } :
            ConcreteRestorationClientRun Statement Proof Payload Result)))
    (by
      intro fuel accumulator request next resume continuations
      exact dispatch_concrete_restoration_completes_within transitionFuel Q
        verifierCalls fuel startProgram environment configuration accumulator
        request resume transitionRoom proverFuelBound verifierFuelBound
        continuations)

/-! ## Root composition and the exact `F` tape -/

/-- The literal root cursor plus its concrete client consumes at most the two
root stage fuels and the uniform restoration allowance.  Executable room-test
failures are ordinary returned protocol results and therefore need no sampled
coordinate. -/
theorem scheduler_native_plain_rom_cursor_completes_within
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls : Nat}
    (transitionFuel Q verifierCalls : Nat)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (limitBounds : SchedulerNativeRootLimitBounds machine globalOracleCalls)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (transitionRoom : 3 ≤ transitionFuel)
    (rootAdversaryFuelBound : machine.adversaryFuel ≤ Q)
    (rootVerifierFuelBound : machine.verifierFuel ≤ verifierCalls)
    (replayAdversaryFuelBound :
      restorationConfiguration.proverReplayFuel ≤ Q)
    (replayVerifierFuelBound :
      restorationConfiguration.verifierFuel ≤ verifierCalls) :
    SchedulerNativeCompletesWithin transitionFuel 3
      (Q + verifierCalls +
        restorationFuel * oneRestorationExposureCap Q verifierCalls)
      (schedulerNativePlainRomCursor machine hidden limitBounds
        restorationConfiguration restorationFuel client) := by
  classical
  let Final := SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
    Result
  let startProgram := machine.blackBox.start hidden machine.observation
  unfold schedulerNativePlainRomCursor
  dsimp only
  by_cases adversaryRoom : StageHasOracleRoom machine.adversaryLimits emptyOracle
      machine.adversaryFuel
  next =>
    rw [dif_pos adversaryRoom]
    apply scheduler_native_completes_within_mono transitionFuel
      (mapped_totalized_machine_completes_within transitionFuel 2
        (verifierCalls +
          restorationFuel * oneRestorationExposureCap Q verifierCalls)
        machine.adversaryLimits limitBounds.adversary .adversary emptyOracle
        startProgram machine.adversaryFuel empty_oracle_history_total_coherent
        (SchedulerStageResult.completed (Final := Final))
        (fun adversaryStage proverFinalOracle proverCoherent =>
          match adversaryStage with
          | .completed adversaryResult =>
              match adversaryResult with
              | .error (.oracleAbort reason) =>
                  .returned (SchedulerNativePlainRomResult.initialFailure
                    (.adversaryOracleAbort reason))
              | .error .timeout =>
                  .returned (SchedulerNativePlainRomResult.initialFailure
                    .adversaryTimeout)
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
                      (fun verifierStage verifierFinalOracle
                          _verifierCoherent =>
                        match verifierStage with
                        | .completed verifierResult =>
                            match verifierResult with
                            | .error (.oracleAbort reason) =>
                                .returned
                                  (SchedulerNativePlainRomResult.initialFailure
                                    (.verifierOracleAbort reason))
                            | .error .timeout =>
                                .returned
                                  (SchedulerNativePlainRomResult.initialFailure
                                    .verifierTimeout)
                            | .ok verifierFinalState =>
                                let rootRuntime := operationalRootRuntime
                                  (machine.tapeIdentity hidden) adversaryValue
                                  proverFinalOracle verifierFinalOracle
                                  verifierFinalState
                                mapSchedulerNativeCursorResult
                                  (fun clientRun =>
                                    SchedulerNativePlainRomResult.completed
                                      rootRuntime clientRun)
                                  (startConcreteRestorationClientFromRoot
                                    (globalOracleCalls := globalOracleCalls)
                                    startProgram machine.environment
                                    rootRuntime.node restorationConfiguration
                                    restorationFuel client))
                  else
                    .returned
                      (SchedulerNativePlainRomResult.initialFailure
                        .verifierRoom))
        adversaryRoom (by omega) ?_)
    · omega
    · omega
    · omega
    intro adversaryStage proverFinalOracle proverCoherent
    cases adversaryStage with
    | completed adversaryResult =>
        cases adversaryResult with
        | error failure =>
            cases failure with
            | oracleAbort reason =>
                apply scheduler_native_completes_within_mono transitionFuel
                  (scheduler_native_returned_completes_within transitionFuel
                    (by omega)
                    (SchedulerNativePlainRomResult.initialFailure
                      (.adversaryOracleAbort reason)))
                · omega
                · omega
                · omega
            | timeout =>
                apply scheduler_native_completes_within_mono transitionFuel
                  (scheduler_native_returned_completes_within transitionFuel
                    (by omega)
                    (SchedulerNativePlainRomResult.initialFailure
                      .adversaryTimeout))
                · omega
                · omega
                · omega
        | ok adversaryValue =>
            simp only
            by_cases verifierRoom : StageHasOracleRoom machine.verifierLimits
                proverFinalOracle machine.verifierFuel
            next =>
              rw [dif_pos verifierRoom]
              apply scheduler_native_completes_within_mono transitionFuel
                (mapped_totalized_machine_completes_within transitionFuel 1
                  (restorationFuel *
                    oneRestorationExposureCap Q verifierCalls)
                  machine.verifierLimits limitBounds.verifier .verifier
                  proverFinalOracle
                  (initialRawFutureFreeProgram machine.environment
                    adversaryValue.rawMessages machine.driverFuel)
                  machine.verifierFuel proverCoherent
                  (SchedulerStageResult.completed (Final := Final))
                  (fun verifierStage verifierFinalOracle _verifierCoherent =>
                    match verifierStage with
                    | .completed verifierResult =>
                      match verifierResult with
                      | .error (.oracleAbort reason) =>
                          .returned
                            (SchedulerNativePlainRomResult.initialFailure
                              (.verifierOracleAbort reason))
                      | .error .timeout =>
                          .returned
                            (SchedulerNativePlainRomResult.initialFailure
                              .verifierTimeout)
                      | .ok verifierFinalState =>
                          let rootRuntime := operationalRootRuntime
                            (machine.tapeIdentity hidden) adversaryValue
                            proverFinalOracle verifierFinalOracle
                            verifierFinalState
                          mapSchedulerNativeCursorResult
                            (fun clientRun =>
                              SchedulerNativePlainRomResult.completed
                                rootRuntime clientRun)
                            (startConcreteRestorationClientFromRoot
                              (globalOracleCalls := globalOracleCalls)
                              startProgram machine.environment rootRuntime.node
                              restorationConfiguration restorationFuel client))
                  verifierRoom (by omega) ?_)
              · omega
              · omega
              · omega
              intro verifierStage verifierFinalOracle verifierCoherent
              cases verifierStage with
              | completed verifierResult =>
                  cases verifierResult with
                  | error failure =>
                      cases failure with
                      | oracleAbort reason =>
                          apply scheduler_native_completes_within_mono
                            transitionFuel
                            (scheduler_native_returned_completes_within
                              transitionFuel (by omega)
                              (SchedulerNativePlainRomResult.initialFailure
                                (.verifierOracleAbort reason)))
                          · omega
                          · omega
                          · omega
                      | timeout =>
                          apply scheduler_native_completes_within_mono
                            transitionFuel
                            (scheduler_native_returned_completes_within
                              transitionFuel (by omega)
                              (SchedulerNativePlainRomResult.initialFailure
                                .verifierTimeout))
                          · omega
                          · omega
                          · omega
                  | ok verifierFinalState =>
                      let rootRuntime := operationalRootRuntime
                        (machine.tapeIdentity hidden) adversaryValue
                        proverFinalOracle verifierFinalOracle verifierFinalState
                      have clientSafe :=
                        concrete_restoration_client_completes_within
                          (globalOracleCalls := globalOracleCalls)
                          transitionFuel Q verifierCalls startProgram
                          machine.environment rootRuntime.node
                          restorationConfiguration restorationFuel client
                          transitionRoom replayAdversaryFuelBound
                          replayVerifierFuelBound
                      exact scheduler_native_completes_within_map transitionFuel
                        1
                        (restorationFuel *
                          oneRestorationExposureCap Q verifierCalls)
                        (fun clientRun =>
                          SchedulerNativePlainRomResult.completed rootRuntime
                            clientRun)
                        clientSafe
            next =>
              rw [dif_neg verifierRoom]
              apply scheduler_native_completes_within_mono transitionFuel
                (scheduler_native_returned_completes_within transitionFuel
                  (by omega)
                  (SchedulerNativePlainRomResult.initialFailure
                    .verifierRoom))
              · omega
              · omega
              · omega
  next =>
    rw [dif_neg adversaryRoom]
    apply scheduler_native_completes_within_mono transitionFuel
      (scheduler_native_returned_completes_within transitionFuel (by omega)
        (SchedulerNativePlainRomResult.initialFailure .adversaryRoom))
    · omega
    · omega
    · omega

/-! ## Literal `F`-tape completion and absence of native failure -/

/-- The exact result-carrying cursor fits the literal unified master-tape cap
`F`.  The two fork coordinates are included per restoration request; cached
prefix replay consumes no master-tape coordinate. -/
theorem exact_plain_rom_cursor_completes_within_F
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape)
    (transitionRoom : 3 ≤ transitionFuel) :
    SchedulerNativeCompletesWithin transitionFuel 3
      (unifiedFull256ExposureCap parameters)
      (exactPlainRomCursor configuration hidden) := by
  have restorationExposureLe :
      configuration.restorationFuel *
          oneRestorationExposureCap parameters.q1ShaCallCap
            deployedFull256VerifierCallCap ≤
        parameters.forkRequestCap *
          oneRestorationExposureCap parameters.q1ShaCallCap
            deployedFull256VerifierCallCap :=
    Nat.mul_le_mul_right _ configuration.bounds.restorationRequests
  have exactExposureLe :
      parameters.q1ShaCallCap + deployedFull256VerifierCallCap +
          configuration.restorationFuel *
            oneRestorationExposureCap parameters.q1ShaCallCap
              deployedFull256VerifierCallCap ≤
        unifiedFull256ExposureCap parameters := by
    calc
      parameters.q1ShaCallCap + deployedFull256VerifierCallCap +
            configuration.restorationFuel *
              oneRestorationExposureCap parameters.q1ShaCallCap
                deployedFull256VerifierCallCap ≤
          parameters.q1ShaCallCap + deployedFull256VerifierCallCap +
            parameters.forkRequestCap *
              oneRestorationExposureCap parameters.q1ShaCallCap
                deployedFull256VerifierCallCap :=
        Nat.add_le_add_left restorationExposureLe _
      _ = unifiedFull256ExposureCap parameters := by
        unfold oneRestorationExposureCap unifiedFull256ExposureCap
          full256MachineFreshCap sameTapeStartCap
        ring
  apply scheduler_native_completes_within_mono transitionFuel
    (scheduler_native_plain_rom_cursor_completes_within transitionFuel
      parameters.q1ShaCallCap deployedFull256VerifierCallCap
      configuration.machine hidden configuration.rootLimitBounds
      configuration.restorationConfiguration configuration.restorationFuel
      configuration.client transitionRoom
      configuration.bounds.rootAdversaryFuel
      configuration.bounds.rootVerifierFuel
      configuration.bounds.replayAdversaryFuel
      configuration.bounds.replayVerifierFuel)
  · omega
  · exact transitionRoom
  · exact exactExposureLe

/-- On the literal finite master tape, every exact plain-ROM execution reaches
an ordinary scheduler return.  Protocol-level room, oracle-abort, timeout, and
restoration failures remain explicit returned values; none is confused with a
native scheduler failure. -/
theorem run_exact_plain_rom_terminal_is_returned
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (transitionRoom : 3 ≤ transitionFuel) :
    ∃ result,
      (runExactPlainRom transitionFuel configuration sample).terminal =
        .returned result := by
  have safe := exact_plain_rom_cursor_completes_within_F transitionFuel
    configuration sample.1 transitionRoom
  have enough :
      unifiedFull256ExposureCap parameters ≤
        (freshAnswerTapeToList sample.2).length := by
    rw [fresh_answer_tape_to_list_length,
      exact_compiler_target_caps_length]
  obtain ⟨result, returned⟩ :=
    safe.2 transitionFuel transitionRoom
      (freshAnswerTapeToList sample.2) enough
  refine ⟨result, ?_⟩
  rw [runExactPlainRom,
    run_scheduler_native_terminal_eq_list transitionFuel
      (exactCompilerTargetCaps parameters).length
      (exactPlainRomCursor configuration sample.1) sample.2]
  exact returned

/-- The experiment-facing native-failure event is empty under the exact
three-transition normalization reserve. -/
theorem exact_plain_rom_native_failure_event_empty
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (transitionRoom : 3 ≤ transitionFuel) :
    exactPlainRomNativeFailureEvent transitionFuel configuration = ∅ := by
  ext sample
  simp only [exactPlainRomNativeFailureEvent, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨reason, failed⟩
  obtain ⟨result, returned⟩ :=
    run_exact_plain_rom_terminal_is_returned transitionFuel configuration sample
      transitionRoom
  rw [returned] at failed
  cases failed

/-- The operational adequacy package supplies the exact three-transition
reserve used by the experiment-facing no-native-failure theorem. -/
theorem exact_plain_rom_native_failure_event_empty_of_adequacy
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel configuration) :
    exactPlainRomNativeFailureEvent transitionFuel configuration = ∅ := by
  apply exact_plain_rom_native_failure_event_empty transitionFuel configuration
  simpa [exactCompilerSufficientTransitionFuel] using
    adequate.schedulerTransitionFuel

#print axioms exact_plain_rom_cursor_completes_within_F
#print axioms run_exact_plain_rom_terminal_is_returned
#print axioms exact_plain_rom_native_failure_event_empty
#print axioms exact_plain_rom_native_failure_event_empty_of_adequacy

end

end AspisK1.V7Tag73ExactPlainRomOperationalCompletion
