import AspisFormal.K1.V7Tag73PrefixTableProvenance
import AspisFormal.K1.V7Tag73OperationalNodeCertificate
import AspisFormal.K1.V7Tag73SchedulerProjectedTraceSafety
import AspisFormal.K1.V7Tag73CompletedFullRunProjection
import AspisFormal.K1.V7Tag73ExactCompilerOperationalCaps

/-!
# Operational table coverage for the concrete Tag-73 restoration client

`TableCoveredByQueryOrProgramming` rules out hidden entries in a lazy-oracle
table: every entry must have an actual query record or an actual programming
record.  This module derives that invariant from the executable operations
used by the concrete restoration client.

The root starts at `emptyOracle`; its prover and verifier boundaries are
actual projected machine prefixes.  A restoration programming base is either
the covered end of its selected parent prover run or the result of an actual
`runPrefix` from the covered parent entry.  Successful pair programming adds
two matching programming records, and the complete prover/verifier stages add
only ordinary query records.

No table-coverage premise, target-event premise, acceptance cover, restore
function, probability coefficient, or extraction conclusion is stored in the
runtime data.  The final section packages the pointwise facts as the node-store
invariant that the concrete dispatcher induction must preserve.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ConcreteClientTableCoverage

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OracleTableProvenance
open AspisK1.V7Tag73PrefixTableProvenance
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73CompletedFullRunProjection
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73ExactCompilerOperationalCaps

noncomputable section

universe u

/-! ## Coverage under the exact concrete operations -/

/-- A returned projected machine prefix preserves table coverage.  Cached and
fresh calls are both handled by the existing `runMachine` invariant; the
projected trace supplies the exact controller/run equation. -/
theorem projected_machine_prefix_preserves_table_coverage
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available)
    (covered : TableCoveredByQueryOrProgramming state) :
    TableCoveredByQueryOrProgramming returned.finalState := by
  have coherent : HistoryTotalCoherent state := by
    exact projected_returned_trace_entry_coherent limits actor fuel state
      program returned.freshQueries returned.result returned.finalState
        returned.steps returned.trace
  have runExact := projected_machine_prefix_returned_run_exact limits actor
    fuel state program available returned coherent
  have preserved :=
    run_machine_preserves_table_covered_by_query_or_programming
      (controllerFromProjectedFreshAnswers state.history
        (returned.freshQueries.map Prod.snd))
      limits actor fuel state program covered
  rw [runExact] at preserved
  exact preserved

/-- One successful concrete half is one successful `programOracle`, hence its
new entry has the matching programming record. -/
theorem program_concrete_half_preserves_table_coverage
    (limits : OracleLimits) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (covered : TableCoveredByQueryOrProgramming state)
    (success : programConcreteHalf limits state input output = .ok nextState) :
    TableCoveredByQueryOrProgramming nextState := by
  apply program_oracle_preserves_table_covered_by_query_or_programming
    limits .extractorReplay state nextState
      { input := input, output := output } covered
  simpa [programConcreteHalf] using success

/-- A successful concrete pair is literally two successful programming
operations in the selected order, so it preserves operational coverage. -/
theorem program_concrete_pair_ready_preserves_table_coverage
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (state afterBoth : OracleState)
    (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256)
    (covered : TableCoveredByQueryOrProgramming state)
    (ready : programConcretePair limits order state outputInput advanceInput
      forkOutput forkAdvance = .ready afterBoth) :
    TableCoveredByQueryOrProgramming afterBoth := by
  by_cases inputsAlias : outputInput = advanceInput
  · simp [programConcretePair, inputsAlias] at ready
  cases outputFound : lookupEntry state outputInput with
  | some entry =>
      simp [programConcretePair, inputsAlias, outputFound] at ready
  | none =>
      cases advanceFound : lookupEntry state advanceInput with
      | some entry =>
          simp [programConcretePair, inputsAlias, outputFound, advanceFound]
            at ready
      | none =>
          cases order with
          | outputThenAdvance =>
              cases first : programConcreteHalf limits state outputInput
                  forkOutput with
              | error reason =>
                  simp [programConcretePair, inputsAlias, outputFound,
                    advanceFound, first] at ready
              | ok afterFirst =>
                  cases second : programConcreteHalf limits afterFirst
                      advanceInput forkAdvance with
                  | error reason =>
                      simp [programConcretePair, inputsAlias, outputFound,
                        advanceFound, first, second] at ready
                  | ok finalState =>
                      have finalExact : finalState = afterBoth := by
                        simpa [programConcretePair, inputsAlias, outputFound,
                          advanceFound, first, second] using ready
                      subst finalState
                      exact program_concrete_half_preserves_table_coverage
                        limits afterFirst afterBoth advanceInput forkAdvance
                        (program_concrete_half_preserves_table_coverage limits
                          state afterFirst outputInput forkOutput covered first)
                        second
          | advanceThenOutput =>
              cases first : programConcreteHalf limits state advanceInput
                  forkAdvance with
              | error reason =>
                  simp [programConcretePair, inputsAlias, outputFound,
                    advanceFound, first] at ready
              | ok afterFirst =>
                  cases second : programConcreteHalf limits afterFirst
                      outputInput forkOutput with
                  | error reason =>
                      simp [programConcretePair, inputsAlias, outputFound,
                        advanceFound, first, second] at ready
                  | ok finalState =>
                      have finalExact : finalState = afterBoth := by
                        simpa [programConcretePair, inputsAlias, outputFound,
                          advanceFound, first, second] using ready
                      subst finalState
                      exact program_concrete_half_preserves_table_coverage
                        limits afterFirst afterBoth outputInput forkOutput
                        (program_concrete_half_preserves_table_coverage limits
                          state afterFirst advanceInput forkAdvance covered first)
                        second

/-! ## Node-local and store-wide invariants -/

/-- All four oracle boundaries retained by one concrete node are covered.
The verifier entry is named separately even though emitted nodes set it equal
to the prover final state; retaining the field makes the invariant robust at
the plain-data boundary. -/
structure ConcreteNodeTablesCovered
    {Statement Proof Payload : Type u}
    (node : ConcreteRestorationNode Statement Proof Payload) : Prop where
  proverEntry : TableCoveredByQueryOrProgramming node.proverEntryOracle
  proverFinal : TableCoveredByQueryOrProgramming node.proverFinalOracle
  verifierEntry : TableCoveredByQueryOrProgramming node.verifierEntryOracle
  verifierFinal : TableCoveredByQueryOrProgramming node.verifierFinalOracle

/-- Every node currently present in the append-only client store is covered. -/
def EveryConcreteNodeTableCovered
    {Statement Proof Payload : Type u}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Prop :=
  ∀ node ∈ accumulator.nodes, ConcreteNodeTablesCovered node

theorem every_concrete_node_table_covered_add_charges
    {Statement Proof Payload : Type u}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge)
    (covered : EveryConcreteNodeTableCovered accumulator) :
    EveryConcreteNodeTableCovered (accumulator.addCharges charges) := by
  intro node member
  exact covered node member

theorem every_concrete_node_table_covered_add_failure
    {Statement Proof Payload : Type u}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (covered : EveryConcreteNodeTableCovered accumulator) :
    EveryConcreteNodeTableCovered (accumulator.addFailure request reason) := by
  intro node member
  exact covered node member

theorem every_concrete_node_table_covered_add_node
    {Statement Proof Payload : Type u}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload)
    (covered : EveryConcreteNodeTableCovered accumulator)
    (childCovered : ConcreteNodeTablesCovered child) :
    EveryConcreteNodeTableCovered (accumulator.addNode child).2 := by
  intro node member
  simp only [ConcreteRestorationAccumulator.addNode, List.mem_append,
    List.mem_singleton] at member
  rcases member with old | rfl
  · exact covered node old
  · exact childCovered

/-- Any proof-free accumulator update that leaves the node list unchanged
preserves the store coverage invariant. -/
theorem every_concrete_node_table_covered_of_nodes_eq
    {Statement Proof Payload : Type u}
    (left right : ConcreteRestorationAccumulator Statement Proof Payload)
    (nodesExact : right.nodes = left.nodes)
    (covered : EveryConcreteNodeTableCovered left) :
    EveryConcreteNodeTableCovered right := by
  intro node member
  apply covered node
  rw [← nodesExact]
  exact member

/-- A ready preparation names a node that is literally present in the current
store.  The proof is obtained from the executable selection theorem, not from
a caller-supplied parent relation. -/
theorem ready_preparation_parent_is_stored
    {Statement Proof Payload : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    prepared.parentNode ∈ accumulator.nodes := by
  have selected :=
    (prepare_concrete_restoration_ready_selection_exact startProgram
      configuration accumulator request prepared ready).1
  unfold ConcreteRestorationAccumulator.node? at selected
  rw [List.getElem?_eq_some_iff] at selected
  rcases selected with ⟨within, valueExact⟩
  have member := List.getElem_mem within
  rw [valueExact] at member
  exact member

/-! ## Exact root and child constructions -/

/-- The operational root built by the plain-ROM scheduler is covered because
its prover begins at `emptyOracle`, and both retained boundaries come from the
two literal projected machine prefixes. -/
theorem operational_root_node_tables_covered
    {TapeIdentity Statement Proof Payload Final : Type u}
    (tapeIdentity : TapeIdentity)
    (adversaryValue :
      CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
    (adversaryLimits verifierLimits : OracleLimits)
    (adversaryFuel verifierFuel : Nat)
    (adversaryProgram : OracleMachine
      (SchedulerStageResult Final
        (Except TotalizedMachineFailure
          (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))))
    (adversaryAnswers : List Digest256)
    (adversary : ProjectedMachinePrefixReturned adversaryLimits .adversary
      adversaryFuel emptyOracle adversaryProgram adversaryAnswers)
    (verifierProgram : OracleMachine
      (SchedulerStageResult Final
        (Except TotalizedMachineFailure FutureFreeVerifierState)))
    (verifierAnswers : List Digest256)
    (verifier : ProjectedMachinePrefixReturned verifierLimits .verifier
      verifierFuel adversary.finalState verifierProgram verifierAnswers)
    (verifierFinalState : FutureFreeVerifierState) :
    ConcreteNodeTablesCovered
      (operationalRootRuntime tapeIdentity adversaryValue adversary.finalState
        verifier.finalState verifierFinalState).node := by
  have entryCovered :=
    empty_oracle_table_covered_by_query_or_programming
  have proverCovered := projected_machine_prefix_preserves_table_coverage
    adversaryLimits .adversary adversaryFuel emptyOracle adversaryProgram
      adversaryAnswers adversary entryCovered
  have verifierCovered := projected_machine_prefix_preserves_table_coverage
    verifierLimits .verifier verifierFuel adversary.finalState verifierProgram
      verifierAnswers verifier proverCovered
  exact
    { proverEntry := entryCovered
      proverFinal := proverCovered
      verifierEntry := proverCovered
      verifierFinal := verifierCovered }

/-- Specialization to the deterministic two-prefix root scanner.  This is the
root coverage fact used by the actual plain-ROM scheduler, with no initial
table premise because the adversary prefix is indexed by `emptyOracle`. -/
theorem completed_root_projected_prefixes_node_tables_covered
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type u}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (prefixes : CompletedRootProjectedPrefixes machine hidden available
      runtime) :
    ConcreteNodeTablesCovered runtime.node := by
  rw [prefixes.runtimeExact]
  exact operational_root_node_tables_covered
    (Final := RootSchedulerResult TapeIdentity Statement Proof Payload)
    (machine.tapeIdentity hidden) prefixes.adversaryValue
    machine.adversaryLimits machine.verifierLimits machine.adversaryFuel
    machine.verifierFuel
    (schedulerStageProgram
      (RootSchedulerResult TapeIdentity Statement Proof Payload)
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation)))
    available prefixes.adversary
    (schedulerStageProgram
      (RootSchedulerResult TapeIdentity Statement Proof Payload)
      (totalizeOracleMachine machine.verifierFuel
        (initialRawFutureFreeProgram machine.environment
          prefixes.adversaryValue.rawMessages machine.driverFuel)))
    prefixes.adversary.remaining prefixes.verifier
    prefixes.verifierFinalStateValue

/-!
The remaining construction theorem follows the actual preparation definition.
In the absent-pair branch the programming base is the parent's complete prover
state.  In the occurrence branch it is the exact `runPrefix` result from the
parent entry state.
-/
theorem ready_preparation_programming_base_tables_covered
    {Statement Proof Payload : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared)
    (parentCovered : ConcreteNodeTablesCovered prepared.parentNode) :
    TableCoveredByQueryOrProgramming prepared.programmingBase := by
  cases selectedNode : accumulator.node? request.nodeId with
  | none =>
      simp [prepareConcreteRestorationFromStartProgram, selectedNode] at ready
  | some parentNode =>
      cases selectedTransition : verifierTransitionAt? parentNode
          request.verifierTransitionIndex with
      | none =>
          simp [prepareConcreteRestorationFromStartProgram, selectedNode,
            selectedTransition] at ready
      | some transition =>
          cases selectedPair : squeezePairInputsOfTransition transition with
          | none =>
              simp [prepareConcreteRestorationFromStartProgram, selectedNode,
                selectedTransition, selectedPair] at ready
          | some pair =>
              rcases pair with ⟨outputInput, advanceInput⟩
              cases selectedOccurrence : firstEitherInputOccurrence outputInput
                  advanceInput parentNode.proverHistory with
              | none =>
                  simp [prepareConcreteRestorationFromStartProgram,
                    selectedNode, selectedTransition, selectedPair,
                    selectedOccurrence] at ready
                  subst prepared
                  exact parentCovered.proverFinal
              | some occurrence =>
                  let prefixRun := runPrefix
                    (recordedPrefixController
                      parentNode.proverEntryOracle.history.length
                      occurrence.before)
                    configuration.oracleLimits .extractorReplay
                    occurrence.before.length parentNode.proverEntryOracle
                    startProgram
                  cases halted : prefixRun.halt with
                  | returned result =>
                      simp [prepareConcreteRestorationFromStartProgram,
                        selectedNode, selectedTransition, selectedPair,
                        selectedOccurrence, prefixRun, halted] at ready
                  | oracleAbort reason =>
                      simp [prepareConcreteRestorationFromStartProgram,
                        selectedNode, selectedTransition, selectedPair,
                        selectedOccurrence, prefixRun, halted] at ready
                  | paused residual =>
                      cases residual with
                      | pure result =>
                          simp [prepareConcreteRestorationFromStartProgram,
                            selectedNode, selectedTransition, selectedPair,
                            selectedOccurrence, prefixRun, halted] at ready
                      | abort reason =>
                          simp [prepareConcreteRestorationFromStartProgram,
                            selectedNode, selectedTransition, selectedPair,
                            selectedOccurrence, prefixRun, halted] at ready
                      | query pendingInput next =>
                          by_cases pendingMismatch :
                              pendingInput ≠ occurrence.chosen.input
                          · simp [prepareConcreteRestorationFromStartProgram,
                              selectedNode, selectedTransition, selectedPair,
                              selectedOccurrence, prefixRun, halted,
                              pendingMismatch] at ready
                          · by_cases traceMismatch : queryAnswerTrace
                                (historySince parentNode.proverEntryOracle
                                  prefixRun.oracle) ≠
                                queryAnswerTrace occurrence.before
                            · simp [prepareConcreteRestorationFromStartProgram,
                                selectedNode, selectedTransition, selectedPair,
                                selectedOccurrence, prefixRun, halted,
                                pendingMismatch, traceMismatch] at ready
                            · simp [prepareConcreteRestorationFromStartProgram,
                                selectedNode, selectedTransition, selectedPair,
                                selectedOccurrence, prefixRun, halted,
                                pendingMismatch, traceMismatch] at ready
                              subst prepared
                              exact
                                run_prefix_preserves_table_covered_by_query_or_programming
                                  (recordedPrefixController
                                    parentNode.proverEntryOracle.history.length
                                    occurrence.before)
                                  configuration.oracleLimits .extractorReplay
                                  occurrence.before.length
                                  parentNode.proverEntryOracle startProgram
                                  parentCovered.proverEntry

/-- Store-level form: the actual prepared parent is selected from the covered
append-only node store, so the programming-base invariant is derived rather
than separately assumed. -/
theorem ready_preparation_programming_base_covered_from_store
    {Statement Proof Payload : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared)
    (allCovered : EveryConcreteNodeTableCovered accumulator) :
    TableCoveredByQueryOrProgramming prepared.programmingBase := by
  apply ready_preparation_programming_base_tables_covered startProgram
    configuration accumulator request prepared ready
  exact allCovered prepared.parentNode
    (ready_preparation_parent_is_stored startProgram configuration accumulator
      request prepared ready)

/-- The exact projected child execution preserves coverage through the two
programmed coordinates, the complete same-tape prover replay, and the restored
future-free verifier suffix. -/
theorem projected_restoration_child_tables_covered
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload)
    (execution : ProjectedRestorationNodeExecution
      (Final := Final) startProgram environment configuration fullTrace
        accumulator child)
    (parentCovered : ConcreteNodeTablesCovered execution.prepared.parentNode) :
    ConcreteNodeTablesCovered child := by
  have baseCovered := ready_preparation_programming_base_tables_covered
    startProgram configuration accumulator execution.prepared.request
      execution.prepared execution.preparationExact parentCovered
  have entryCovered :=
    program_concrete_pair_ready_preserves_table_coverage
      configuration.oracleLimits configuration.pairProgrammingOrder
      execution.prepared.programmingBase child.proverEntryOracle
      execution.prepared.outputInput execution.prepared.advanceInput
      execution.scheduled.configuration.forkOutput
      execution.scheduled.configuration.forkAdvance baseCovered
      execution.programmingExact
  have proverCovered := projected_machine_prefix_preserves_table_coverage
    configuration.oracleLimits .extractorReplay
      configuration.proverReplayFuel child.proverEntryOracle
      (schedulerStageProgram Final
        (totalizeOracleMachine configuration.proverReplayFuel startProgram))
      (machineFreshAnswers execution.proverRecords) execution.proverPrefix
      entryCovered
  rw [execution.proverFinalExact] at proverCovered
  have verifierCovered := projected_machine_prefix_preserves_table_coverage
    configuration.oracleLimits .verifier configuration.verifierFuel
      child.verifierEntryOracle
      (schedulerStageProgram Final
        (totalizeOracleMachine configuration.verifierFuel
          (driveRawFutureFree environment child.adversaryValue.rawMessages
            configuration.driverFuel child.verifierEntryState)))
      (machineFreshAnswers execution.verifierRecords) execution.verifierPrefix
      (by simpa [execution.verifierEntryOracleExact] using proverCovered)
  rw [execution.verifierFinalExact] at verifierCovered
  exact
    { proverEntry := entryCovered
      proverFinal := proverCovered
      verifierEntry := by
        simpa [execution.verifierEntryOracleExact] using proverCovered
      verifierFinal := verifierCovered }

/-! ## Induction over the actual concrete client dispatcher -/

/-- Every ordinary result reachable below the concrete client cursor has a
covered node store.  The projected-trace safety grammar is essential: unlike
the result-only grammar, its machine constructor supplies an actual returned
machine-prefix certificate rather than an arbitrary callback state. -/
def ConcreteClientPreservesEveryNodeTableCoverage
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (cursor : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result)) : Prop :=
  EveryConcreteNodeTableCovered accumulator →
    SchedulerNativeCursorAllProjectedTracedReturned
      (fun run _trace => EveryConcreteNodeTableCovered run.accumulator) cursor

theorem failure_continuation_preserves_node_table_coverage
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (continuations : ∀ reply nextAccumulator,
      ConcreteClientPreservesEveryNodeTableCoverage nextAccumulator
        (resume reply nextAccumulator))
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    ConcreteClientPreservesEveryNodeTableCoverage accumulator
      (resume (.failed reason) (accumulator.addFailure request reason)) := by
  intro covered
  exact continuations (.failed reason)
    (accumulator.addFailure request reason)
    (every_concrete_node_table_covered_add_failure accumulator request reason
      covered)

/-- One actual executable restoration dispatch preserves table coverage on
every projected scheduler return, including every explicit failure branch. -/
theorem dispatch_one_concrete_restoration_preserves_node_table_coverage
    {Statement Proof Payload Result : Type u}
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
    (continuations : ∀ reply nextAccumulator,
      ConcreteClientPreservesEveryNodeTableCoverage nextAccumulator
        (resume reply nextAccumulator)) :
    ConcreteClientPreservesEveryNodeTableCoverage accumulator
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  intro covered
  have failureSafe : ∀ failureRequest reason nextAccumulator,
      EveryConcreteNodeTableCovered nextAccumulator →
      SchedulerNativeCursorAllProjectedTracedReturned
        (fun run _trace => EveryConcreteNodeTableCovered run.accumulator)
        (resume (.failed reason)
          (nextAccumulator.addFailure failureRequest reason)) := by
    intro failureRequest reason nextAccumulator nextCovered
    exact continuations (.failed reason)
      (nextAccumulator.addFailure failureRequest reason)
      (every_concrete_node_table_covered_add_failure nextAccumulator
        failureRequest reason nextCovered)
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration,
        preparationExact]
      apply failureSafe request reason
      exact every_concrete_node_table_covered_add_charges accumulator
        [.prefixReplayQueries prefixSteps, .restart prefixRestarts] covered
  | ready prepared =>
      have parentStored := ready_preparation_parent_is_stored startProgram
        configuration accumulator request prepared preparationExact
      have parentCovered := covered prepared.parentNode parentStored
      have programmingBaseCovered :=
        ready_preparation_programming_base_tables_covered startProgram
          configuration accumulator request prepared preparationExact
            parentCovered
      let prefixRestarts := if prepared.prefixRun.isSome then 1 else 0
      let withPrefix := accumulator.addCharges
        [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
      have withPrefixCovered : EveryConcreteNodeTableCovered withPrefix := by
        exact every_concrete_node_table_covered_add_charges accumulator
          [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
          covered
      simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration,
        preparationExact]
      unfold dispatchPreparedRestoration
      by_cases prefixCoherent : HistoryTotalCoherent prepared.programmingBase
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
            apply SchedulerNativeCursorAllProjectedTracedReturned.forkPair
            intro scheduled frozenExact outputExact advanceExact templateExact
            let afterCoordinates := withPrefix.addCharges
              [.forkUniformCoordinates 2]
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                scheduled.configuration.forkOutput
                scheduled.configuration.forkAdvance with
            | failed reason inserted =>
                simp only [programmed]
                have beforeFailure : EveryConcreteNodeTableCovered
                    (afterCoordinates.addCharges
                      [.programmedPoints inserted]) := by
                  apply every_concrete_node_table_covered_of_nodes_eq
                    accumulator
                    (afterCoordinates.addCharges [.programmedPoints inserted])
                    rfl covered
                exact continuations (.failed reason)
                  ((afterCoordinates.addCharges
                    [.programmedPoints inserted]).addFailure prepared.request
                      reason)
                  (every_concrete_node_table_covered_add_failure
                    (afterCoordinates.addCharges [.programmedPoints inserted])
                    prepared.request reason beforeFailure)
            | ready afterBoth =>
                simp only [programmed]
                have afterBothCovered :=
                  program_concrete_pair_ready_preserves_table_coverage
                    configuration.oracleLimits
                    configuration.pairProgrammingOrder
                    prepared.programmingBase afterBoth prepared.outputInput
                    prepared.advanceInput scheduled.configuration.forkOutput
                    scheduled.configuration.forkAdvance programmingBaseCovered
                    programmed
                let afterProgramming := afterCoordinates.addCharges
                  [.programmedPoints 2]
                by_cases afterCoherent : HistoryTotalCoherent afterBoth
                next =>
                  simp only [afterCoherent, if_pos]
                  by_cases proverRoom : StageHasOracleRoom
                      configuration.oracleLimits afterBoth
                      configuration.proverReplayFuel
                  next =>
                    simp only [proverRoom, if_pos]
                    let atProverStart := afterProgramming.addCharges [.restart 1]
                    apply SchedulerNativeCursorAllProjectedTracedReturned.machine
                    intro available proverPrefix
                    have proverFinalCovered :=
                      projected_machine_prefix_preserves_table_coverage
                        configuration.oracleLimits .extractorReplay
                        configuration.proverReplayFuel afterBoth
                        (schedulerStageProgram
                          (ConcreteRestorationClientRun Statement Proof Payload
                            Result)
                          (totalizeOracleMachine
                            configuration.proverReplayFuel startProgram))
                        available proverPrefix afterBothCovered
                    cases proverPrefix.result with
                    | completed proverResult =>
                      let proverQueries :=
                        (historySince afterBoth proverPrefix.finalState).length
                      let afterProver := atProverStart.addCharges
                        [.completeFromStartQueries proverQueries]
                      have afterProverCovered :
                          EveryConcreteNodeTableCovered afterProver := by
                        apply every_concrete_node_table_covered_of_nodes_eq
                          accumulator afterProver rfl covered
                      cases proverResult with
                      | error failure =>
                        cases failure with
                        | oracleAbort reason =>
                          exact continuations
                            (.failed (.proverReplayAbort reason))
                            (afterProver.addFailure prepared.request
                              (.proverReplayAbort reason))
                            (every_concrete_node_table_covered_add_failure
                              afterProver prepared.request
                              (.proverReplayAbort reason) afterProverCovered)
                        | timeout =>
                          exact continuations (.failed .proverReplayTimeout)
                            (afterProver.addFailure prepared.request
                              .proverReplayTimeout)
                            (every_concrete_node_table_covered_add_failure
                              afterProver prepared.request .proverReplayTimeout
                              afterProverCovered)
                      | ok adversaryValue =>
                        simp only
                        by_cases bindingMismatch :
                            FixedBindings.ofContext
                                adversaryValue.rawMessages.context ≠
                              prepared.restoredState.current.bindings
                        next =>
                          rw [dif_pos bindingMismatch]
                          exact continuations
                            (.failed .restoredBindingMismatch)
                            (afterProver.addFailure prepared.request
                              .restoredBindingMismatch)
                            (every_concrete_node_table_covered_add_failure
                              afterProver prepared.request
                              .restoredBindingMismatch afterProverCovered)
                        next =>
                          rw [dif_neg bindingMismatch]
                          by_cases verifierRoom : StageHasOracleRoom
                              configuration.oracleLimits proverPrefix.finalState
                              configuration.verifierFuel
                          next =>
                            rw [dif_pos verifierRoom]
                            apply
                              SchedulerNativeCursorAllProjectedTracedReturned.machine
                            intro verifierAvailable verifierPrefix
                            have verifierFinalCovered :=
                              projected_machine_prefix_preserves_table_coverage
                                configuration.oracleLimits .verifier
                                configuration.verifierFuel
                                proverPrefix.finalState
                                (schedulerStageProgram
                                  (ConcreteRestorationClientRun Statement Proof
                                    Payload Result)
                                  (totalizeOracleMachine
                                    configuration.verifierFuel
                                    (driveRawFutureFree environment
                                      adversaryValue.rawMessages
                                      configuration.driverFuel
                                      prepared.restoredState)))
                                verifierAvailable verifierPrefix
                                proverFinalCovered
                            cases verifierPrefix.result with
                            | completed verifierResult =>
                              let verifierQueries :=
                                (historySince proverPrefix.finalState
                                  verifierPrefix.finalState).length
                              let afterVerifier := afterProver.addCharges
                                [.verifierSuffixQueries verifierQueries]
                              have afterVerifierCovered :
                                  EveryConcreteNodeTableCovered
                                    afterVerifier := by
                                apply
                                  every_concrete_node_table_covered_of_nodes_eq
                                    accumulator afterVerifier rfl covered
                              cases verifierResult with
                              | error failure =>
                                cases failure with
                                | oracleAbort reason =>
                                  exact continuations
                                    (.failed (.verifierSuffixAbort reason))
                                    (afterVerifier.addFailure prepared.request
                                      (.verifierSuffixAbort reason))
                                    (every_concrete_node_table_covered_add_failure
                                      afterVerifier prepared.request
                                      (.verifierSuffixAbort reason)
                                      afterVerifierCovered)
                                | timeout =>
                                  exact continuations
                                    (.failed .verifierSuffixTimeout)
                                    (afterVerifier.addFailure prepared.request
                                      .verifierSuffixTimeout)
                                    (every_concrete_node_table_covered_add_failure
                                      afterVerifier prepared.request
                                      .verifierSuffixTimeout
                                      afterVerifierCovered)
                              | ok verifierFinalState =>
                                let transitionCount :=
                                  verifierFinalState.transitions.length
                                let node : ConcreteRestorationNode Statement Proof
                                    Payload :=
                                  { parentRequest := some prepared.request
                                    adversaryValue := adversaryValue
                                    proverEntryOracle := afterBoth
                                    proverFinalOracle := proverPrefix.finalState
                                    verifierEntryOracle := proverPrefix.finalState
                                    verifierFinalOracle := verifierPrefix.finalState
                                    verifierEntryState := prepared.restoredState
                                    verifierFinalState := verifierFinalState }
                                let charged := afterVerifier.addCharges
                                  [.verifierTransitions transitionCount]
                                let added := charged.addNode node
                                have nodeCovered :
                                    ConcreteNodeTablesCovered node :=
                                  { proverEntry := afterBothCovered
                                    proverFinal := proverFinalCovered
                                    verifierEntry := proverFinalCovered
                                    verifierFinal := verifierFinalCovered }
                                have chargedCovered :
                                    EveryConcreteNodeTableCovered charged := by
                                  apply
                                    every_concrete_node_table_covered_of_nodes_eq
                                      accumulator charged rfl covered
                                have addedCovered :
                                    EveryConcreteNodeTableCovered added.2 := by
                                  exact every_concrete_node_table_covered_add_node
                                    charged node chargedCovered nodeCovered
                                exact continuations (.added added.1) added.2
                                  addedCovered
                          next =>
                            rw [dif_neg verifierRoom]
                            exact continuations (.failed .verifierSuffixRoom)
                              (afterProver.addFailure prepared.request
                                .verifierSuffixRoom)
                              (every_concrete_node_table_covered_add_failure
                                afterProver prepared.request .verifierSuffixRoom
                                afterProverCovered)
                  next =>
                    simp only [proverRoom, if_neg]
                    have beforeFailure : EveryConcreteNodeTableCovered
                        afterProgramming := by
                      apply every_concrete_node_table_covered_of_nodes_eq
                        accumulator afterProgramming rfl covered
                    exact continuations (.failed .proverReplayRoom)
                      (afterProgramming.addFailure prepared.request
                        .proverReplayRoom)
                      (every_concrete_node_table_covered_add_failure
                        afterProgramming prepared.request .proverReplayRoom
                        beforeFailure)
                next =>
                  simp only [afterCoherent, if_neg]
                  have beforeFailure : EveryConcreteNodeTableCovered
                      afterProgramming := by
                    apply every_concrete_node_table_covered_of_nodes_eq
                      accumulator afterProgramming rfl covered
                  exact continuations (.failed .incoherentProgrammedOracle)
                    (afterProgramming.addFailure prepared.request
                      .incoherentProgrammedOracle)
                    (every_concrete_node_table_covered_add_failure
                      afterProgramming prepared.request
                      .incoherentProgrammedOracle beforeFailure)
          next =>
            simp only [pairRoom, if_neg]
            exact failureSafe prepared.request .pairExposureLimit withPrefix
              withPrefixCovered
        next =>
          simp only [globalLimit, if_neg]
          exact failureSafe prepared.request .globalLimitTooSmall withPrefix
            withPrefixCovered
      next =>
        simp only [prefixCoherent, if_neg]
        exact failureSafe prepared.request .incoherentPrefixOracle withPrefix
          withPrefixCovered

/-- The private fuel-bounded client interpreter preserves coverage for every
actual projected return.  Restoration-fuel exhaustion only appends a failure
record and therefore also preserves the invariant. -/
theorem concrete_restoration_client_preserves_every_node_table_coverage
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootCovered : ConcreteNodeTablesCovered root)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result) :
    SchedulerNativeCursorAllProjectedTracedReturned
      (fun run _trace => EveryConcreteNodeTableCovered run.accumulator)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls) startProgram environment root
        configuration restorationFuel client) := by
  let motive := fun (_fuel : Nat)
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (_residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
      ConcreteClientPreservesEveryNodeTableCoverage accumulator cursor
  have induction :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment root
      configuration restorationFuel client motive
      (by
        intro fuel accumulator result covered
        apply SchedulerNativeCursorAllProjectedTracedReturned.returned
        intro answers
        exact covered)
      (by
        intro accumulator request next covered
        apply SchedulerNativeCursorAllProjectedTracedReturned.returned
        intro answers
        exact every_concrete_node_table_covered_add_failure accumulator request
          .restorationFuelExhausted covered)
      (by
        intro fuel accumulator request next resume continuations
        exact dispatch_one_concrete_restoration_preserves_node_table_coverage
          startProgram environment configuration accumulator request resume
            continuations)
  apply induction
  intro node member
  have nodeExact : node = root := by
    simpa [initialRestorationAccumulatorFromRoot] using member
  simpa [nodeExact] using rootCovered

/-- A normally returned concrete client run has covered root, programming
bases and emitted child states.  This is the direct operational theorem used
by the programming-freshness composition; coverage is constructed above and
is not an argument. -/
theorem returned_concrete_restoration_client_every_node_table_covered
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls remaining : Nat}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootCovered : ConcreteNodeTablesCovered root)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (tape : FreshAnswerTape Digest256 remaining)
    (run : ConcreteRestorationClientRun Statement Proof Payload Result)
    (returned :
      (runSchedulerNative transitionFuel remaining
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalOracleCalls) startProgram environment root
          configuration restorationFuel client) tape).terminal =
        .returned run) :
    EveryConcreteNodeTableCovered run.accumulator := by
  have safe := concrete_restoration_client_preserves_every_node_table_coverage
    (globalOracleCalls := globalOracleCalls) startProgram environment root
      rootCovered configuration restorationFuel client
  exact run_scheduler_native_respects_projected_traced_returned
    (fun result _trace => EveryConcreteNodeTableCovered result.accumulator)
      transitionFuel positive _ safe tape run returned

/-- Fully operational specialization: the root coverage premise of the
generic client theorem is discharged by the actual empty-oracle root prefix
scanner. -/
theorem returned_concrete_client_from_completed_root_prefixes_tables_covered
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result :
      Type u}
    {globalOracleCalls remaining : Nat}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape) (rootAnswers : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (prefixes : CompletedRootProjectedPrefixes machine hidden rootAnswers
      runtime)
    (configuration : ConcreteRestorationConfiguration)
    (restorationFuel : Nat)
    (client : ConcreteRestorationClient Result)
    (tape : FreshAnswerTape Digest256 remaining)
    (run : ConcreteRestorationClientRun Statement Proof Payload Result)
    (returned :
      (runSchedulerNative transitionFuel remaining
        (startConcreteRestorationClientFromRoot
          (globalOracleCalls := globalOracleCalls)
          (machine.blackBox.start hidden machine.observation)
          machine.environment runtime.node configuration restorationFuel client)
        tape).terminal = .returned run) :
    EveryConcreteNodeTableCovered run.accumulator := by
  exact returned_concrete_restoration_client_every_node_table_covered
    transitionFuel positive
    (machine.blackBox.start hidden machine.observation) machine.environment
    runtime.node
    (completed_root_projected_prefixes_node_tables_covered machine hidden
      rootAnswers runtime prefixes)
    configuration restorationFuel client tape run returned

/-- Exact accessor consumed by the programming-freshness theorem.  Once the
actual client induction proves the store invariant, coverage of a selected
child entry is no longer an independent premise. -/
theorem selected_node_prover_entry_table_covered
    {Statement Proof Payload : Type u}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (nodeId : Nat) (node : ConcreteRestorationNode Statement Proof Payload)
    (allCovered : EveryConcreteNodeTableCovered accumulator)
    (selected : accumulator.node? nodeId = some node) :
    TableCoveredByQueryOrProgramming node.proverEntryOracle := by
  apply (allCovered node ?_).proverEntry
  unfold ConcreteRestorationAccumulator.node? at selected
  rw [List.getElem?_eq_some_iff] at selected
  rcases selected with ⟨within, valueExact⟩
  have member := List.getElem_mem within
  rw [valueExact] at member
  exact member

#print axioms projected_machine_prefix_preserves_table_coverage
#print axioms program_concrete_pair_ready_preserves_table_coverage
#print axioms operational_root_node_tables_covered
#print axioms completed_root_projected_prefixes_node_tables_covered
#print axioms ready_preparation_parent_is_stored
#print axioms ready_preparation_programming_base_tables_covered
#print axioms ready_preparation_programming_base_covered_from_store
#print axioms projected_restoration_child_tables_covered
#print axioms dispatch_one_concrete_restoration_preserves_node_table_coverage
#print axioms concrete_restoration_client_preserves_every_node_table_coverage
#print axioms returned_concrete_restoration_client_every_node_table_covered
#print axioms returned_concrete_client_from_completed_root_prefixes_tables_covered
#print axioms selected_node_prover_entry_table_covered

end

end AspisK1.V7Tag73ConcreteClientTableCoverage
