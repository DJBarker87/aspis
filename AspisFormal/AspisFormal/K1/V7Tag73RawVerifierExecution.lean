import AspisFormal.K1.V7Tag73RawFutureFreeDriver
import AspisFormal.K1.V7Tag73VerifierOracleStability
import AspisFormal.K1.V7Tag73SequentialOracleRuns

/-!
# One actual raw-prover / future-free-verifier Tag-73 execution

This module joins the two operational phases used by the classical-ROM
compiler.  The adversary first runs from its one closed hidden tape and
returns only raw prover-owned messages.  The future-free verifier then starts
from the exact oracle state at adversary halt and executes the literal Tag-73
driver.

The record below contains only normal-return equations and explicit resource
controls.  Schedule exhaustion, deployed acceptance, witness extraction and
the Fiat--Shamir cover are deliberately absent.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawVerifierExecution

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73SequentialOracleRuns

noncomputable section

/-! ## The concrete two-phase run -/

/-- A normally returned raw prover run followed by one normally returned
future-free verifier run over the exact post-prover oracle state.  The two
fuel fields have different meanings: `driverFuel` bounds protocol
microsteps, while `verifierFuel` bounds actual verifier oracle calls. -/
structure RawVerifierExecution
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    (source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload) where
  adversaryValue :
    CheckedRawTag73AdversaryReturnedValue Statement Proof Payload
  adversaryReturned :
    source.firstExecution.halt = .returned adversaryValue
  environment : FutureFreeEnvironment
  verifierController : AdaptiveController
  verifierLimits : OracleLimits
  driverFuel : Nat
  verifierFuel : Nat
  finalState : FutureFreeVerifierState
  verifierReturned :
    (runMachine verifierController verifierLimits .verifier verifierFuel
      source.firstExecution.oracle
      (initialRawFutureFreeProgram environment adversaryValue.rawMessages
        driverFuel)).halt = .returned finalState

def RawVerifierExecution.verifierRun
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    MachineRun FutureFreeVerifierState :=
  runMachine execution.verifierController execution.verifierLimits .verifier
    execution.verifierFuel source.firstExecution.oracle
    (initialRawFutureFreeProgram execution.environment
      execution.adversaryValue.rawMessages execution.driverFuel)

def RawVerifierExecution.q1
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (_execution : RawVerifierExecution source) : List QueryRecord :=
  freezeAdversaryQ1 source.firstExecution.oracle

def RawVerifierExecution.verifierHistory
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) : List QueryRecord :=
  historySince source.firstExecution.oracle execution.verifierRun.oracle

def RawVerifierExecution.finalTable
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) : FixedOracleTable :=
  fixedTableOfOracleState execution.verifierRun.oracle

@[simp] theorem raw_verifier_execution_is_literal_run
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    execution.verifierRun =
      runMachine execution.verifierController execution.verifierLimits
        .verifier execution.verifierFuel source.firstExecution.oracle
        (initialRawFutureFreeProgram execution.environment
          execution.adversaryValue.rawMessages execution.driverFuel) := by
  rfl

theorem raw_verifier_execution_normally_returns
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    execution.verifierRun.halt = .returned execution.finalState := by
  exact execution.verifierReturned

/-! ## Same tape, frozen Q1 and fixed public instance -/

theorem raw_verifier_execution_uses_source_hidden_tape
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (_execution : RawVerifierExecution source) :
    source.capability.start source.observation =
      source.blackBox.start source.hiddenTape source.observation := by
  exact raw_source_capability_uses_same_hidden_tape source

@[simp] theorem raw_verifier_execution_tape_identity
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (_execution : RawVerifierExecution source) :
    source.capability.tapeIdentity = source.tapeIdentity := by
  exact raw_source_capability_identity source

@[simp] theorem raw_verifier_execution_q1_is_exact_adversary_halt_history
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    execution.q1 = freezeAdversaryQ1 source.firstExecution.oracle := by
  rfl

theorem raw_verifier_execution_q1_only_has_adversary_calls
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    ∀ record ∈ execution.q1, record.actor = .adversary := by
  intro record member
  exact frozen_q1_contains_only_adversary_calls source.firstExecution.oracle
    record member

theorem raw_verifier_execution_preserves_public_bindings
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    let value := execution.adversaryValue
    let bindings := FixedBindings.ofContext value.rawMessages.context
    bindings.programId = value.1.publicProof.publicInstance.context.programId ∧
      bindings.releaseBinding =
        value.1.publicProof.publicInstance.context.releaseBinding ∧
      bindings.statementDigest =
        value.1.publicProof.publicInstance.context.statementDigest ∧
      bindings.attemptId =
        value.1.publicProof.publicInstance.context.attemptId ∧
      bindings.proofAccountId =
        value.1.publicProof.publicInstance.context.attemptId := by
  exact checked_raw_return_preserves_public_bindings execution.adversaryValue

/-! ## Literal verifier query path -/

/-- The exact ordered query path made by the future-free verifier. -/
theorem raw_verifier_execution_has_exact_query_path
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    ∃ pairs : List (ShaInput × ShaOutput),
      MachineQueryPath
          (initialRawFutureFreeProgram execution.environment
            execution.adversaryValue.rawMessages execution.driverFuel)
          pairs execution.finalState ∧
      queryAnswerTrace execution.verifierHistory = pairs ∧
      (∀ record ∈ execution.verifierHistory,
        record.actor = .verifier) ∧
      ∀ pair ∈ pairs,
        tableLookup execution.finalTable pair.1 = some pair.2 := by
  simpa [RawVerifierExecution.verifierRun,
    RawVerifierExecution.verifierHistory, RawVerifierExecution.finalTable]
    using
      run_machine_returned_has_exact_query_path execution.verifierController
        execution.verifierLimits .verifier execution.verifierFuel
        source.firstExecution.oracle
        (initialRawFutureFreeProgram execution.environment
          execution.adversaryValue.rawMessages execution.driverFuel)
        execution.finalState execution.verifierReturned

/-- The exact query path is simultaneously a chronological operational trace
of prover submissions and forced verifier actions. -/
theorem raw_verifier_execution_has_operational_trace
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    ∃ pairs : List (ShaInput × ShaOutput),
      queryAnswerTrace execution.verifierHistory = pairs ∧
      FutureFreeOperationalTrace execution.environment
        execution.adversaryValue.rawMessages
        (initialFutureFreeVerifierState
          (FixedBindings.ofContext execution.adversaryValue.rawMessages.context))
        pairs execution.finalState := by
  obtain ⟨pairs, path, history, _actors, _answers⟩ :=
    raw_verifier_execution_has_exact_query_path execution
  exact ⟨pairs, history,
    initial_raw_future_free_path_is_operational_trace execution.environment
      execution.adversaryValue.rawMessages execution.driverFuel pairs
      execution.finalState path⟩

/-- The normally returned final verifier state has a nonempty complete-state
history and carries the same fixed instance in every snapshot. -/
theorem raw_verifier_execution_has_exact_run_invariant
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    FutureFreeRunInvariant
      (FixedBindings.ofContext execution.adversaryValue.rawMessages.context)
      execution.finalState := by
  obtain ⟨pairs, path, _history, _actors, _answers⟩ :=
    raw_verifier_execution_has_exact_query_path execution
  exact initial_raw_future_free_return_has_exact_run_invariant
    execution.environment execution.adversaryValue.rawMessages
    execution.driverFuel pairs execution.finalState path

/-! ## Exact table/history/runtime accounting -/

theorem raw_verifier_execution_final_oracle_is_fresh_extension
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    execution.verifierRun.oracle.table = source.firstExecution.oracle.table ++
        verifierFreshTableEntries source.firstExecution.oracle
          execution.verifierRun.oracle ∧
      (∀ record ∈ execution.verifierHistory,
        record.actor = .verifier ∧
          (record.origin = .fresh →
            lookupEntry source.firstExecution.oracle record.input = none)) ∧
      execution.verifierHistory.length ≤ execution.verifierRun.steps := by
  simpa [RawVerifierExecution.verifierRun,
    RawVerifierExecution.verifierHistory] using
      (run_machine_exact_fresh_extension execution.verifierController
        execution.verifierLimits .verifier execution.verifierFuel
        source.firstExecution.oracle
        (initialRawFutureFreeProgram execution.environment
          execution.adversaryValue.rawMessages execution.driverFuel))

theorem raw_verifier_execution_steps_le_fuel
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    execution.verifierRun.steps ≤ execution.verifierFuel := by
  simpa [RawVerifierExecution.verifierRun] using
    run_machine_steps_le_fuel execution.verifierController
      execution.verifierLimits .verifier execution.verifierFuel
      source.firstExecution.oracle
      (initialRawFutureFreeProgram execution.environment
        execution.adversaryValue.rawMessages execution.driverFuel)

theorem raw_verifier_execution_query_count_le_fuel
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    execution.verifierHistory.length ≤ execution.verifierFuel := by
  exact (raw_verifier_execution_final_oracle_is_fresh_extension execution).2.2.trans
    (raw_verifier_execution_steps_le_fuel execution)

#print axioms raw_verifier_execution_normally_returns
#print axioms raw_verifier_execution_uses_source_hidden_tape
#print axioms raw_verifier_execution_tape_identity
#print axioms raw_verifier_execution_q1_only_has_adversary_calls
#print axioms raw_verifier_execution_preserves_public_bindings
#print axioms raw_verifier_execution_has_exact_query_path
#print axioms raw_verifier_execution_has_operational_trace
#print axioms raw_verifier_execution_has_exact_run_invariant
#print axioms raw_verifier_execution_final_oracle_is_fresh_extension
#print axioms raw_verifier_execution_steps_le_fuel
#print axioms raw_verifier_execution_query_count_le_fuel

end

end AspisK1.V7Tag73RawVerifierExecution
