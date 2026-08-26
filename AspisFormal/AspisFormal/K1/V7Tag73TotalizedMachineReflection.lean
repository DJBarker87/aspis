import AspisFormal.K1.V7Tag73SchedulerNativePlainRomExperiment

/-!
# Reflection for totalized oracle-machine stages

The scheduler turns protocol aborts and fuel exhaustion into ordinary result
values so that its callbacks can record exact failures.  A successful
`.ok` result must nevertheless be an execution of the original program, not
of a weaker interface.  This module proves that fact directly from the two
interpreters.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73TotalizedMachineReflection

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SequentialOracleRuns
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment

noncomputable section

/-- If the totalized program normally returns `.ok result`, the literal
original program has exactly the same final oracle, step count and successful
result under the same controller. -/
theorem run_machine_totalized_ok_reflects
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) :
    ∀ (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
      (result : Result) (finalState : OracleState) (steps : Nat),
      runMachine controller limits actor fuel state
          (totalizeOracleMachine fuel program) =
        { halt := .returned (.ok result)
          oracle := finalState
          steps := steps } →
      runMachine controller limits actor fuel state program =
        { halt := .returned result
          oracle := finalState
          steps := steps } := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program result finalState steps returned
      cases program with
      | pure value =>
          simpa [totalizeOracleMachine, runMachine] using returned
      | abort reason =>
          simp [totalizeOracleMachine, runMachine] at returned
      | query input next =>
          simp [totalizeOracleMachine, runMachine] at returned
  | succ fuel ih =>
      intro state program result finalState steps returned
      cases program with
      | pure value =>
          simpa [totalizeOracleMachine, runMachine] using returned
      | abort reason =>
          simp [totalizeOracleMachine, runMachine] at returned
      | query input next =>
          simp only [totalizeOracleMachine, runMachine] at returned ⊢
          cases queried : queryOracle controller limits actor state input with
          | error reason =>
              simp [queried] at returned
          | ok outputAndState =>
              rcases outputAndState with ⟨output, nextState⟩
              simp only [queried]
              simp only [queried] at returned
              generalize tailEq :
                runMachine controller limits actor fuel nextState
                    (totalizeOracleMachine fuel (next output)) = tailRun
                at returned
              rcases tailRun with ⟨tailHalt, tailOracle, tailSteps⟩
              cases tailHalt with
              | oracleAbort reason => simp at returned
              | outOfFuel => simp at returned
              | returned totalizedResult =>
                  cases totalizedResult with
                  | error failure => simp at returned
                  | ok returnedResult =>
                      simp only [MachineRun.mk.injEq,
                        MachineHalt.returned.injEq, Except.ok.injEq] at returned
                      have reflected := ih nextState (next output) result
                        tailOracle tailSteps (by
                          simpa [returned.1] using tailEq)
                      rw [reflected]
                      simpa [returned.2.1, returned.2.2]

/-! ## Concrete projected controllers for the root segments -/

universe u

def rootAdversaryFreshAnswers
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : List Digest256 :=
  freshAnswerEnumeration
    (historySince emptyOracle runtime.proverFinalOracle)

def rootVerifierFreshAnswers
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : List Digest256 :=
  freshAnswerEnumeration
    (historySince runtime.proverFinalOracle runtime.verifierFinalOracle)

def rootAdversaryProjectedController
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : AdaptiveController :=
  controllerFromProjectedFreshAnswers emptyOracle.history
    (rootAdversaryFreshAnswers runtime)

def rootVerifierProjectedController
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : AdaptiveController :=
  controllerFromProjectedFreshAnswers runtime.proverFinalOracle.history
    (rootVerifierFreshAnswers runtime)

/-- The ordinary raw source reconstructed from the first scheduler segment.
Its controller is computed from that segment's actual fresh history; it is
not supplied by a caller. -/
def projectedRootSource
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) :
    RawTag73SameTapeSource HiddenTape TapeIdentity Observation Statement Proof
      Payload where
  blackBox := machine.blackBox
  hiddenTape := hidden
  tapeIdentity := machine.tapeIdentity hidden
  observation := machine.observation
  controller := rootAdversaryProjectedController runtime
  oracleLimits := machine.adversaryLimits
  firstRunFuel := machine.adversaryFuel
  initialOracle := emptyOracle

/-- Exact target of the scheduler-segment reconstruction theorem.  It contains
only two executable run equations under controllers derived from the two
actual runtime histories.  The final compiler theorem must prove this
predicate from `runSchedulerNativePlainRom`; it may not assume it. -/
def RootProjectedTotalizedRuns
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : Prop :=
  ∃ adversarySteps verifierSteps,
    runMachine (rootAdversaryProjectedController runtime)
        machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
        (totalizeOracleMachine machine.adversaryFuel
          (machine.blackBox.start hidden machine.observation)) =
      { halt := .returned (.ok runtime.adversaryValue)
        oracle := runtime.proverFinalOracle
        steps := adversarySteps } ∧
    runMachine (rootVerifierProjectedController runtime)
        machine.verifierLimits .verifier machine.verifierFuel
        runtime.proverFinalOracle
        (totalizeOracleMachine machine.verifierFuel
          (initialRawFutureFreeProgram machine.environment
            runtime.adversaryValue.rawMessages machine.driverFuel)) =
      { halt := .returned (.ok runtime.verifierFinalState)
        oracle := runtime.verifierFinalOracle
        steps := verifierSteps }

/-- Once the scheduler-segment theorem establishes the two concrete
totalized equations, reflection produces the pre-existing ordinary raw
prover/verifier execution.  This is an existence theorem because Lean does
not eliminate the propositional run predicate into runtime data. -/
theorem projected_root_runs_give_raw_verifier_execution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime) :
    ∃ execution : RawVerifierExecution
        (projectedRootSource machine hidden runtime),
      execution.adversaryValue = runtime.adversaryValue ∧
        execution.finalState = runtime.verifierFinalState := by
  rcases runs with ⟨adversarySteps, verifierSteps, adversaryRun, verifierRun⟩
  have reflectedAdversary := run_machine_totalized_ok_reflects
    (rootAdversaryProjectedController runtime) machine.adversaryLimits
    .adversary machine.adversaryFuel emptyOracle
    (machine.blackBox.start hidden machine.observation)
    runtime.adversaryValue runtime.proverFinalOracle adversarySteps adversaryRun
  have reflectedVerifier := run_machine_totalized_ok_reflects
    (rootVerifierProjectedController runtime) machine.verifierLimits .verifier
    machine.verifierFuel runtime.proverFinalOracle
    (initialRawFutureFreeProgram machine.environment
      runtime.adversaryValue.rawMessages machine.driverFuel)
    runtime.verifierFinalState runtime.verifierFinalOracle verifierSteps
    verifierRun
  let execution : RawVerifierExecution
      (projectedRootSource machine hidden runtime) :=
    { adversaryValue := runtime.adversaryValue
      adversaryReturned := by
        change (runMachine (rootAdversaryProjectedController runtime)
          machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
          (machine.blackBox.start hidden machine.observation)).halt =
            .returned runtime.adversaryValue
        rw [reflectedAdversary]
      environment := machine.environment
      verifierController := rootVerifierProjectedController runtime
      verifierLimits := machine.verifierLimits
      driverFuel := machine.driverFuel
      verifierFuel := machine.verifierFuel
      finalState := runtime.verifierFinalState
      verifierReturned := by
        change (runMachine (rootVerifierProjectedController runtime)
          machine.verifierLimits .verifier machine.verifierFuel
          (runMachine (rootAdversaryProjectedController runtime)
            machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
            (machine.blackBox.start hidden machine.observation)).oracle
          (initialRawFutureFreeProgram machine.environment
            runtime.adversaryValue.rawMessages machine.driverFuel)).halt =
              .returned runtime.verifierFinalState
        rw [reflectedAdversary, reflectedVerifier] }
  exact ⟨execution, rfl, rfl⟩

theorem projected_root_runs_imply_root_invariant
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime) :
    SchedulerNativePlainRomRootInvariant runtime := by
  obtain ⟨execution, adversaryExact, finalExact⟩ :=
    projected_root_runs_give_raw_verifier_execution machine hidden runtime runs
  have invariant := raw_verifier_execution_has_exact_run_invariant execution
  unfold SchedulerNativePlainRomRootInvariant
  simpa [adversaryExact, finalExact] using invariant

#print axioms run_machine_totalized_ok_reflects
#print axioms projected_root_runs_imply_root_invariant

end

end AspisK1.V7Tag73TotalizedMachineReflection
