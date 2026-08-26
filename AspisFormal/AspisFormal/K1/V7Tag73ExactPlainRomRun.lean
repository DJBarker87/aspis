import AspisFormal.K1.V7Tag73SchedulerNativePlainRomExperiment
import AspisFormal.K1.V7Tag73ExactCompilerResources

/-!
# Exact finite plain-ROM run for deployed Tag-73

This module ties the operational scheduler-native Tag-73 cursor to the final
`Q,R` resource arithmetic.  A sample consists only of a hidden adversary tape
and the independent uniform full-256 master tape.  The result is computed by
the literal prover, the dependent future-free verifier, and the concrete
restoration client; there is no caller-supplied outcome, world, restoration
function, acceptance cover, or extractor result map.

The bounds below are deliberately stage-local.  `Q` bounds every literal
same-tape adversary start, `1511` bounds each future-free verifier execution,
and `R` bounds restoration requests.  The resulting scheduler is indexed by
the exact global call cap `G`, while its sampled tape has the exact unified
exposure length `F`.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactPlainRomRun

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources

noncomputable section

/-! ## One exact operational configuration -/

/-- Resource facts that connect the executable machine to `Q,R`.  These are
ordinary adversary/extractor budget hypotheses, not success assumptions.  In
particular, no field says that a run returns, accepts, restores successfully,
or extracts a witness. -/
structure ExactPlainRomOperationalBounds
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type}
    (parameters : ExactCompilerResourceParameters)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (restorationConfiguration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat) : Prop where
  rootAdversaryTotalCalls :
    machine.adversaryLimits.totalCalls ≤
      globalFull256OracleCallCap parameters
  rootVerifierTotalCalls :
    machine.verifierLimits.totalCalls ≤
      globalFull256OracleCallCap parameters
  replayTotalCalls :
    restorationConfiguration.oracleLimits.totalCalls ≤
      globalFull256OracleCallCap parameters
  rootAdversaryFuel :
    machine.adversaryFuel ≤ parameters.q1ShaCallCap
  rootVerifierFuel :
    machine.verifierFuel ≤ deployedFull256VerifierCallCap
  replayAdversaryFuel :
    restorationConfiguration.proverReplayFuel ≤ parameters.q1ShaCallCap
  replayVerifierFuel :
    restorationConfiguration.verifierFuel ≤ deployedFull256VerifierCallCap
  restorationRequests : restorationFuel ≤ parameters.forkRequestCap

/-- All executable inputs to one fixed-instance plain-ROM experiment.  The
client is a finite free state-restoration algorithm; its only observation is
the concrete success/failure reply returned by the dispatcher. -/
structure ExactPlainRomConfiguration
    (HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type)
    (parameters : ExactCompilerResourceParameters) where
  machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
    Statement Proof Payload
  restorationConfiguration : ConcreteRestorationConfiguration
  restorationFuel : Nat
  client : ConcreteRestorationClient Result
  bounds : ExactPlainRomOperationalBounds parameters machine
    restorationConfiguration restorationFuel

theorem ExactPlainRomConfiguration.rootLimitBounds
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    SchedulerNativeRootLimitBounds configuration.machine
      (globalFull256OracleCallCap parameters) where
  adversary := configuration.bounds.rootAdversaryTotalCalls
  verifier := configuration.bounds.rootVerifierTotalCalls

/-! ## The one nonanticipating cursor -/

/-- The exact operational cursor selected by a hidden tape.  Its type fixes
the global call cap `G` before any uniform master-tape coordinate is read. -/
def exactPlainRomCursor
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    SchedulerNativeCursor (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result) :=
  schedulerNativePlainRomCursor configuration.machine hidden
    configuration.rootLimitBounds configuration.restorationConfiguration
    configuration.restorationFuel configuration.client

/-- Result-free projection used by the causal target tree.  This is an erasure
of the same cursor, not an independently supplied probability experiment. -/
def exactPlainRomExposureCursor
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    UnifiedExposureCursor (globalFull256OracleCallCap parameters) :=
  (exactPlainRomCursor configuration hidden).erase

/-- Initial Fiat--Shamir run only.  The pure client performs no restoration,
so this cursor returns immediately after the actual prover and dependent
verifier callbacks have built the root runtime. -/
def exactPlainRomRootCursor
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    SchedulerNativeCursor (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        PUnit) :=
  schedulerNativePlainRomCursor configuration.machine hidden
    configuration.rootLimitBounds configuration.restorationConfiguration 0
    (.pure PUnit.unit)

@[simp] theorem exact_plain_rom_cursor_uses_literal_same_tape_start
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    configuration.machine.blackBox.start hidden
        configuration.machine.observation =
      (closeSameTapeStart configuration.machine.blackBox hidden
        (configuration.machine.tapeIdentity hidden)).start
          configuration.machine.observation := by
  rfl

/-! ## Fixed finite joint experiment -/

/-- Run the exact result-carrying cursor on the master tape contained in one
joint sample.  The tape length is definitionally the target-cap-list length;
the theorem below identifies it with the closed form `F`. -/
def runExactPlainRom
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        Result) :=
  runSchedulerNative transitionFuel
    (exactCompilerTargetCaps parameters).length
    (exactPlainRomCursor configuration sample.1) sample.2

/-- Standalone initial-run interpreter on the same hidden/master-tape sample.
It is the operational source of the noninteractive acceptance event; later
restoration failures cannot retroactively change this result. -/
def runExactPlainRomRoot
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement Proof Payload
        PUnit) :=
  runSchedulerNative transitionFuel
    (exactCompilerTargetCaps parameters).length
    (exactPlainRomRootCursor configuration sample.1) sample.2

/-- Root runtime returned by the actual initial-only cursor, if both initial
machine stages completed. -/
def exactPlainRomRoot?
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    Option
      (SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
        Payload) :=
  match (runExactPlainRomRoot transitionFuel configuration sample).terminal with
  | .returned (.completed root _clientRun) => some root
  | .returned (.initialFailure _) | .failed _ => none

/-- Operational terminal projection.  Unlike the historical `world`, this is
computed from the scheduler run and retains the actual root and accumulator. -/
def exactPlainRomCompleted?
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    Option
      (SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof Payload ×
        ConcreteRestorationClientRun Statement Proof Payload Result) :=
  match (runExactPlainRom transitionFuel configuration sample).terminal with
  | .returned (.completed root clientRun) => some (root, clientRun)
  | .returned (.initialFailure _) | .failed _ => none

/-- Native scheduler failures are distinguished from protocol-level initial
failures and from restoration failures recorded in the returned accumulator. -/
def exactPlainRomNativeFailureEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ reason,
    (runExactPlainRom transitionFuel configuration sample).terminal =
      .failed reason}

def exactPlainRomInitialFailureEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ reason,
    (runExactPlainRom transitionFuel configuration sample).terminal =
      .returned (.initialFailure reason)}

theorem exact_plain_rom_master_tape_length_is_F
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (_configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    (exactCompilerTargetCaps parameters).length =
      unifiedFull256ExposureCap parameters := by
  exact exact_compiler_target_caps_length parameters

theorem exact_plain_rom_trace_length
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (runExactPlainRom transitionFuel configuration sample).trace.length =
      unifiedFull256ExposureCap parameters := by
  rw [runExactPlainRom, run_scheduler_native_trace_length_exact]
  exact exact_compiler_target_caps_length parameters

theorem exact_plain_rom_trace_answers_are_master_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (runExactPlainRom transitionFuel configuration sample).trace.map
        UnifiedExposureRecord.answer = freshAnswerTapeToList sample.2 := by
  exact run_scheduler_native_answers_are_exact_tape transitionFuel
    (exactCompilerTargetCaps parameters).length
    (exactPlainRomCursor configuration sample.1) sample.2

/-- The probability analysis and the result-carrying experiment observe the
same literal exposure trace. -/
theorem exact_plain_rom_trace_is_erased_exposure_trace
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (runExactPlainRom transitionFuel configuration sample).trace =
      runUnifiedExposureTrace transitionFuel
        (exactCompilerTargetCaps parameters).length
        (exactPlainRomExposureCursor configuration sample.1) sample.2 := by
  exact run_scheduler_native_trace_eq_erased_unified_trace transitionFuel
    (exactCompilerTargetCaps parameters).length
    (exactPlainRomCursor configuration sample.1) sample.2

/-- The probability target is built from the literal erasure of the cursor
that produces `runExactPlainRom`. -/
def exactPlainRomTargetEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactCompilerTargetEvent parameters transitionFuel
    (exactPlainRomExposureCursor configuration)

theorem exact_plain_rom_target_probability_le_exact_count
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactPlainRomTargetEvent transitionFuel configuration) ≤
      exactCompilerExactCountError parameters := by
  exact exact_compiler_target_probability_le_exact_count hiddenLaw parameters
    transitionFuel (exactPlainRomExposureCursor configuration)

theorem exact_plain_rom_target_probability_le_raw_error
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactPlainRomTargetEvent transitionFuel configuration) ≤
      exactCompilerPositiveExposureError parameters := by
  exact exact_compiler_target_probability_le_div_two_pow_256 hiddenLaw
    parameters transitionFuel (exactPlainRomExposureCursor configuration)

theorem exact_plain_rom_operational_budget_fields
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    configuration.machine.adversaryFuel ≤ parameters.q1ShaCallCap ∧
      configuration.machine.verifierFuel ≤ 1511 ∧
      configuration.restorationConfiguration.proverReplayFuel ≤
        parameters.q1ShaCallCap ∧
      configuration.restorationConfiguration.verifierFuel ≤ 1511 ∧
      configuration.restorationFuel ≤ parameters.forkRequestCap := by
  exact ⟨configuration.bounds.rootAdversaryFuel,
    configuration.bounds.rootVerifierFuel,
    configuration.bounds.replayAdversaryFuel,
    configuration.bounds.replayVerifierFuel,
    configuration.bounds.restorationRequests⟩

#print axioms exact_plain_rom_cursor_uses_literal_same_tape_start
#print axioms exact_plain_rom_master_tape_length_is_F
#print axioms exact_plain_rom_trace_length
#print axioms exact_plain_rom_trace_answers_are_master_tape
#print axioms exact_plain_rom_trace_is_erased_exposure_trace
#print axioms exact_plain_rom_target_probability_le_exact_count
#print axioms exact_plain_rom_target_probability_le_raw_error
#print axioms exact_plain_rom_operational_budget_fields

end

end AspisK1.V7Tag73ExactPlainRomRun
