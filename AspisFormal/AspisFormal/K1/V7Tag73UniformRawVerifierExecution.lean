import AspisFormal.K1.V7Tag73RawDriverResourceBound
import AspisFormal.K1.V7Tag73OperationalOracleExposure

/-!
# Uniform-tape construction of the raw Tag-73 two-phase execution

One finite tape supplies every fresh 256-bit answer to both the same-hidden-
tape prover and the dependent future-free verifier run.  The verifier program
is chosen only after the literal raw prover value returns.  A successful
executable result constructs `RawVerifierExecution`; no caller supplies a
query history, final verifier state, or run equation.

This is a deterministic interpreter over a fixed answer tape.  Uniformity is
provided later by sampling that tape with `uniformDigestFreshTape`.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73UniformRawVerifierExecution

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73RawDriverResourceBound
open AspisK1.V7Tag73OperationalOracleExposure

noncomputable section

/-! ## Fixed machine description and tape-indexed source -/

structure UniformRawVerifierMachine
    (HiddenTape TapeIdentity Observation Statement Proof Payload : Type*) where
  blackBox : SameTapeBlackBox HiddenTape Observation
    (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
  tapeIdentity : HiddenTape → TapeIdentity
  observation : Observation
  environment : FutureFreeEnvironment
  adversaryLimits : OracleLimits
  verifierLimits : OracleLimits
  adversaryFuel : Nat
  driverFuel : Nat
  verifierFuel : Nat

def UniformRawVerifierMachine.source
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (tape : FreshAnswerTape Digest256 steps) :
    RawTag73SameTapeSource HiddenTape TapeIdentity Observation Statement Proof
      Payload where
  blackBox := machine.blackBox
  hiddenTape := hidden
  tapeIdentity := machine.tapeIdentity hidden
  observation := machine.observation
  controller := controllerFromFreshAnswerTape tape
  oracleLimits := machine.adversaryLimits
  firstRunFuel := machine.adversaryFuel
  initialOracle := emptyOracle

def UniformRawVerifierMachine.verifierRunFor
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (tape : FreshAnswerTape Digest256 steps)
    (value : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload) :
    MachineRun FutureFreeVerifierState :=
  let source := machine.source hidden tape
  runMachine (controllerFromFreshAnswerTape tape) machine.verifierLimits
    .verifier machine.verifierFuel source.firstExecution.oracle
    (initialRawFutureFreeProgram machine.environment value.rawMessages
      machine.driverFuel)

/-! ## Total executable result and its successful branch -/

/-- Total two-phase interpreter.  Failure to return normally in either phase
is represented by `none`; success returns exactly the two machine values. -/
def runUniformRawProverThenVerifier?
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (tape : FreshAnswerTape Digest256 steps) :
    Option
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload ×
        FutureFreeVerifierState) :=
  let source := machine.source hidden tape
  match source.firstExecution.halt with
  | .returned value =>
      match (machine.verifierRunFor hidden tape value).halt with
      | .returned finalState => some (value, finalState)
      | .oracleAbort _ | .outOfFuel => none
  | .oracleAbort _ | .outOfFuel => none

/-- Proof object recovered by inverting the total interpreter.  Both
equalities are equations of actual `runMachine` evaluations. -/
structure UniformRawVerifierSuccess
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (tape : FreshAnswerTape Digest256 steps) where
  adversaryValue :
    CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  finalState : FutureFreeVerifierState
  adversaryReturned :
    (machine.source hidden tape).firstExecution.halt =
      .returned adversaryValue
  verifierReturned :
    (machine.verifierRunFor hidden tape adversaryValue).halt =
      .returned finalState

theorem uniform_raw_prover_then_verifier_success_iff
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (tape : FreshAnswerTape Digest256 steps) :
    (∃ value finalState,
      runUniformRawProverThenVerifier? machine hidden tape =
        some (value, finalState)) ↔
      Nonempty (UniformRawVerifierSuccess machine hidden tape) := by
  constructor
  · rintro ⟨value, finalState, returned⟩
    dsimp only [runUniformRawProverThenVerifier?] at returned
    split at returned
    next adversaryValue adversaryReturned =>
      split at returned
      next verifierState verifierReturned =>
        simp only [Option.some.injEq, Prod.mk.injEq] at returned
        rcases returned with ⟨rfl, rfl⟩
        exact ⟨⟨adversaryValue, verifierState,
          adversaryReturned, verifierReturned⟩⟩
      all_goals simp at returned
    all_goals simp at returned
  · rintro ⟨success⟩
    exact ⟨success.adversaryValue, success.finalState, by
      dsimp only [runUniformRawProverThenVerifier?]
      simp [success.adversaryReturned, success.verifierReturned]⟩

/-! ## Construct the existing operational execution -/

def UniformRawVerifierSuccess.toRawVerifierExecution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {tape : FreshAnswerTape Digest256 steps}
    (success : UniformRawVerifierSuccess machine hidden tape) :
    RawVerifierExecution (machine.source hidden tape) where
  adversaryValue := success.adversaryValue
  adversaryReturned := success.adversaryReturned
  environment := machine.environment
  verifierController := controllerFromFreshAnswerTape tape
  verifierLimits := machine.verifierLimits
  driverFuel := machine.driverFuel
  verifierFuel := machine.verifierFuel
  finalState := success.finalState
  verifierReturned := success.verifierReturned

@[simp] theorem uniform_success_execution_uses_exact_controller
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {tape : FreshAnswerTape Digest256 steps}
    (success : UniformRawVerifierSuccess machine hidden tape) :
    success.toRawVerifierExecution.verifierController =
      controllerFromFreshAnswerTape tape := by
  rfl

@[simp] theorem uniform_success_execution_starts_empty_oracle
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {tape : FreshAnswerTape Digest256 steps}
    (_success : UniformRawVerifierSuccess machine hidden tape) :
    (machine.source hidden tape).initialOracle = emptyOracle := by
  rfl

@[simp] theorem uniform_success_execution_uses_exact_tape_identity
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {tape : FreshAnswerTape Digest256 steps}
    (_success : UniformRawVerifierSuccess machine hidden tape) :
    (machine.source hidden tape).tapeIdentity = machine.tapeIdentity hidden := by
  rfl

/-! ## One exact uniform tape across both phases -/

theorem uniform_success_first_history_matches_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {tape : FreshAnswerTape Digest256 steps}
    (_success : UniformRawVerifierSuccess machine hidden tape) :
    FreshHistoryMatchesTape tape
      (machine.source hidden tape).firstExecution.oracle := by
  exact run_machine_with_uniform_tape_preserves_fresh_history_contents tape
    machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
    ((machine.source hidden tape).capability.start machine.observation)
    (empty_oracle_within_fresh_answer_tape tape)
    (empty_oracle_fresh_history_matches_tape tape)

theorem uniform_success_final_history_matches_same_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {tape : FreshAnswerTape Digest256 steps}
    (success : UniformRawVerifierSuccess machine hidden tape) :
    FreshHistoryMatchesTape tape
      success.toRawVerifierExecution.verifierRun.oracle := by
  have firstWithin :=
    run_machine_with_uniform_tape_preserves_exposure_bound tape
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      ((machine.source hidden tape).capability.start machine.observation)
      (empty_oracle_within_fresh_answer_tape tape)
  have firstMatches := uniform_success_first_history_matches_tape success
  exact run_machine_with_uniform_tape_preserves_fresh_history_contents tape
    machine.verifierLimits .verifier machine.verifierFuel
    (machine.source hidden tape).firstExecution.oracle
    (initialRawFutureFreeProgram machine.environment
      success.adversaryValue.rawMessages machine.driverFuel)
    firstWithin firstMatches

theorem uniform_success_final_fresh_calls_le_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {tape : FreshAnswerTape Digest256 steps}
    (success : UniformRawVerifierSuccess machine hidden tape) :
    success.toRawVerifierExecution.verifierRun.oracle.freshCalls ≤ steps := by
  have firstWithin :=
    run_machine_with_uniform_tape_preserves_exposure_bound tape
      machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
      ((machine.source hidden tape).capability.start machine.observation)
      (empty_oracle_within_fresh_answer_tape tape)
  exact (run_machine_with_uniform_tape_preserves_exposure_bound tape
    machine.verifierLimits .verifier machine.verifierFuel
    (machine.source hidden tape).firstExecution.oracle
    (initialRawFutureFreeProgram machine.environment
      success.adversaryValue.rawMessages machine.driverFuel)
    firstWithin).2

theorem uniform_success_verifier_queries_le_driver_fuel
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {steps : Nat}
    {machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    {hidden : HiddenTape} {tape : FreshAnswerTape Digest256 steps}
    (success : UniformRawVerifierSuccess machine hidden tape) :
    success.toRawVerifierExecution.verifierHistory.length ≤
      2 * machine.driverFuel := by
  exact raw_verifier_execution_query_path_length_le_two_mul_driver_fuel
    success.toRawVerifierExecution

#print axioms uniform_raw_prover_then_verifier_success_iff
#print axioms uniform_success_execution_uses_exact_controller
#print axioms uniform_success_execution_starts_empty_oracle
#print axioms uniform_success_execution_uses_exact_tape_identity
#print axioms uniform_success_first_history_matches_tape
#print axioms uniform_success_final_history_matches_same_tape
#print axioms uniform_success_final_fresh_calls_le_tape
#print axioms uniform_success_verifier_queries_le_driver_fuel

end

end AspisK1.V7Tag73UniformRawVerifierExecution
