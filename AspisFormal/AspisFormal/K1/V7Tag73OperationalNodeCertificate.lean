import AspisFormal.K1.V7Tag73ProjectedMachinePrefix
import AspisFormal.K1.V7Tag73ConcreteRestorationClient
import AspisFormal.K1.V7Tag73SchedulerTraceFactorization

/-!
# Proof-only operational certificates for concrete Tag-73 restoration nodes

The live restoration accumulator intentionally stores only plain runtime data.
This module states the stronger external certificate that a child node must
eventually receive from the actual scheduler trace: concrete preparation and
pair programming, a complete literal-start prover prefix, and a complete
future-free verifier suffix from the derived restored state.

No certificate below is a runtime field and no caller can choose a restore
function, verifier state, controller, trace cover, acceptance event, or
compiler conclusion.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73OperationalNodeCertificate

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization

noncomputable section

universe u

/-- A successful fresh fork may repeat any immutable-root request.  At a
descendant, transition zero is the squeeze inherited from the parent restore
and is already programmed in that descendant's entry table, so a further
successful fresh fork must select a later transition. -/
def StructurallyFreshRestorationRequest
    (request : ConcreteRestorationRequest) : Prop :=
  request.nodeId = 0 ∨ request.verifierTransitionIndex ≠ 0

/-- `childTransition` is the replay of the exact parent squeeze checkpoint.
The response may change after reprogramming, but the complete preceding
snapshot and squeeze action are the same. -/
def IsInheritedRestoredSqueeze
    (parentTransition childTransition : FutureFreeTransition) : Prop :=
  ∃ owner block parentReply childReply,
    parentTransition.event =
        .verifier (.squeezePair owner block) parentReply ∧
      childTransition.event =
        .verifier (.squeezePair owner block) childReply ∧
      childTransition.before = parentTransition.before

/-- The two records emitted by one actual adjacent scheduler fork pair. -/
def scheduledPairRecords (scheduled : ScheduledForkCoins) :
    List UnifiedExposureRecord :=
  [.forkOutput scheduled.frozenHistory scheduled.outputInput
      scheduled.advanceInput scheduled.template scheduled.forkOutput,
    .forkAdvance scheduled]

/-- An actual chronological trace contains this exact adjacent fork pair. -/
def AdjacentScheduledPairInTrace
    (scheduled : ScheduledForkCoins)
    (trace : List UnifiedExposureRecord) : Prop :=
  ∃ before after,
    trace = before ++ scheduledPairRecords scheduled ++ after

/-- A programming-history entry is exactly one half of a scheduled pair. -/
def ScheduledPairPrograms
    (scheduled : ScheduledForkCoins) (record : ProgrammingRecord) : Prop :=
  record.actor = .extractorReplay ∧
    ((record.input = scheduled.outputInput ∧
        record.output = scheduled.forkOutput) ∨
      (record.input = scheduled.advanceInput ∧
        record.output = scheduled.forkAdvance))

/-- Recover the 256-bit transcript state encoded by the deployed typed
`S || 0x01`, `S || 0x02` pair inputs. -/
def ScheduledPairInputState
    (scheduled : ScheduledForkCoins) (state : Digest256) : Prop :=
  scheduled.outputInput = bytes state ++ [domSqueeze] ∧
    scheduled.advanceInput = bytes state ++ [domAdvance]

/-- Only nonpadding master-tape coordinates count as causal digest sources. -/
def ActiveExposureAnswer
    (digest : Digest256) (records : List UnifiedExposureRecord) : Prop :=
  ∃ record ∈ records,
    (match record with
      | .padding _answer => False
      | _ => record.answer = digest)

/-- One machine slice consists solely of fresh oracle exposures by `actor`.
Cached calls are absent because the scheduler normalizes them without reading
a master-tape coordinate. -/
def OnlyMachineFreshActor
    (actor : QueryActor) (records : List UnifiedExposureRecord) : Prop :=
  ∀ record ∈ records,
    ∃ input answer, record = .machineFresh actor input answer

/-- Exact execution evidence for one nonroot node.  Both machine-prefix
objects contain their own future-free projected trace, so callback outputs and
oracle boundaries cannot be supplied independently of the executed programs.
-/
structure ProjectedRestorationNodeExecution
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload) : Type u where
  prepared : PreparedConcreteRestoration Statement Proof Payload
  preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
        accumulator prepared.request =
      .ready prepared
  parentRequestExact : child.parentRequest = some prepared.request
  restoredEntryExact : child.verifierEntryState = prepared.restoredState
  traceBeforePair : List UnifiedExposureRecord
  proverRecords : List UnifiedExposureRecord
  verifierRecords : List UnifiedExposureRecord
  traceAfterVerifier : List UnifiedExposureRecord
  scheduled : ScheduledForkCoins
  scheduledFrozenHistoryExact :
    scheduled.frozenHistory = prepared.programmingBase.history
  scheduledOutputInputExact : scheduled.outputInput = prepared.outputInput
  scheduledAdvanceInputExact : scheduled.advanceInput = prepared.advanceInput
  scheduledTemplateExact :
    scheduled.template = canonicalForkTemplate configuration
  scheduledInputStateExact :
    ScheduledPairInputState scheduled prepared.transition.before.core.digest
  fullTraceExact :
    fullTrace = traceBeforePair ++ scheduledPairRecords scheduled ++
      proverRecords ++ verifierRecords ++ traceAfterVerifier
  programmingExact :
    programConcretePair configuration.oracleLimits
        configuration.pairProgrammingOrder prepared.programmingBase
        prepared.outputInput prepared.advanceInput
        scheduled.configuration.forkOutput
        scheduled.configuration.forkAdvance =
      .ready child.proverEntryOracle
  proverPrefix : ProjectedMachinePrefixReturned configuration.oracleLimits
    .extractorReplay configuration.proverReplayFuel child.proverEntryOracle
    (schedulerStageProgram Final
      (totalizeOracleMachine configuration.proverReplayFuel startProgram))
    (machineFreshAnswers proverRecords)
  proverRecordsOnly : OnlyMachineFreshActor .extractorReplay proverRecords
  proverQueriesExact :
    machineFreshQueryAnswers proverRecords = proverPrefix.freshQueries
  proverReturned : proverPrefix.result = .completed (.ok child.adversaryValue)
  proverFinalExact : proverPrefix.finalState = child.proverFinalOracle
  verifierEntryOracleExact :
    child.verifierEntryOracle = child.proverFinalOracle
  restoredBindingExact :
    FixedBindings.ofContext child.adversaryValue.rawMessages.context =
      child.verifierEntryState.current.bindings
  verifierPrefix : ProjectedMachinePrefixReturned configuration.oracleLimits
    .verifier configuration.verifierFuel child.verifierEntryOracle
    (schedulerStageProgram Final
      (totalizeOracleMachine configuration.verifierFuel
        (driveRawFutureFree environment child.adversaryValue.rawMessages
          configuration.driverFuel child.verifierEntryState)))
    (machineFreshAnswers verifierRecords)
  verifierRecordsOnly : OnlyMachineFreshActor .verifier verifierRecords
  verifierQueriesExact :
    machineFreshQueryAnswers verifierRecords = verifierPrefix.freshQueries
  verifierReturned :
    verifierPrefix.result = .completed (.ok child.verifierFinalState)
  verifierFinalExact : verifierPrefix.finalState = child.verifierFinalOracle

/-- The additional causal provenance needed to turn global target cleanliness
into programming freshness.  It is separated from the scheduler-native base
execution because these fields require the dedicated query/transition
provenance induction rather than mere cursor inversion. -/
structure CausallyProvenancedRestorationNodeExecution
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload) : Type u where
  base : ProjectedRestorationNodeExecution (Final := Final) startProgram environment
    configuration fullTrace accumulator child
  requestIsStructurallyFresh :
    StructurallyFreshRestorationRequest base.prepared.request
  programmingHistoryHasEarlierPairProvenance :
    ∀ record ∈ child.proverEntryOracle.programmingHistory,
      ∃ (earlier : ScheduledForkCoins)
          (earlierBefore earlierAfter : List UnifiedExposureRecord)
          (inputState : Digest256),
        base.traceBeforePair ++ scheduledPairRecords base.scheduled =
          earlierBefore ++ scheduledPairRecords earlier ++ earlierAfter ∧
        ScheduledPairPrograms earlier record ∧
        ScheduledPairInputState earlier inputState ∧
        (inputState = zeroDigest256 ∨
          ActiveExposureAnswer inputState earlierBefore)
  positiveTransitionDigestProvenance :
    ∀ transitionIndex transition,
      transitionIndex ≠ 0 →
      verifierTransitionAt? child transitionIndex = some transition →
      transition.before.core.digest = base.scheduled.forkAdvance ∨
        ActiveExposureAnswer transition.before.core.digest
          (base.proverRecords ++ base.verifierRecords)

/-- The first-child transition is a separate adequate-fuel consequence.  It
is deliberately not part of the base execution certificate: with driver fuel
zero the child can be returned with no transition at all. -/
structure AdequateFirstChildTransition
    {Statement Proof Payload : Type u}
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload) : Type u where
  transition : FutureFreeTransition
  transitionExact : verifierTransitionAt? child 0 = some transition
  inherited : IsInheritedRestoredSqueeze prepared.transition transition

/-- Base scheduler provenance plus the first-transition consequence available
only after the caller has proved adequate driver fuel for the canonical
future-free path. -/
structure AdequateProjectedRestorationNodeExecution
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload) : Type u where
  base : ProjectedRestorationNodeExecution (Final := Final) startProgram environment
    configuration fullTrace accumulator child
  first : AdequateFirstChildTransition base.prepared child

/-- Every nonroot node in the final plain accumulator has the exact two-stage
operational certificate above.  The root is handled by
`RootProjectedTotalizedRuns` and is deliberately excluded here. -/
def EveryNodeOperational
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Prop :=
  ∀ child ∈ accumulator.nodes,
    child.parentRequest ≠ none →
      Nonempty (ProjectedRestorationNodeExecution
        (Final := Final) startProgram environment configuration fullTrace
        accumulator child)

/-- Adequate-fuel strengthening.  This predicate is never claimed for an
arbitrary `driverFuel`; its construction theorem must consume the canonical
driver-fuel coverage proof. -/
def EveryNodeOperationalWithAdequateFirst
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Prop :=
  ∀ child ∈ accumulator.nodes,
    child.parentRequest ≠ none →
      Nonempty (AdequateProjectedRestorationNodeExecution
        (Final := Final) startProgram environment configuration fullTrace
        accumulator child)

/-- Strong causal provenance for every nonroot node, still separate from the
adequate-first-transition theorem. -/
def EveryNodeOperationalWithCausalProvenance
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (fullTrace : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload) :
    Prop :=
  ∀ child ∈ accumulator.nodes,
    child.parentRequest ≠ none →
      Nonempty (CausallyProvenancedRestorationNodeExecution
        (Final := Final) startProgram environment configuration fullTrace
        accumulator child)

/-! ## Immediate consequences of the trace-indexed certificate -/

/-- A successful preparation retains the literal paired-squeeze inputs selected
from the indexed parent transition.  This is stronger than merely saying that
the transition is some squeeze: it links both byte strings stored in the
prepared runtime value to that transition's exact preceding digest. -/
theorem prepare_from_start_ready_pair_inputs_exact
    {Statement Proof Payload : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    squeezePairInputsOfTransition prepared.transition =
      some (prepared.outputInput, prepared.advanceInput) := by
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
                  exact selectedPair
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
                              exact selectedPair

/-- Literal squeeze inputs determine one common preceding transcript state. -/
theorem squeeze_pair_inputs_exact_give_input_state
    (transition : FutureFreeTransition)
    (outputInput advanceInput : ShaInput)
    (exactInputs : squeezePairInputsOfTransition transition =
      some (outputInput, advanceInput)) :
    outputInput = bytes transition.before.core.digest ++ [domSqueeze] ∧
      advanceInput = bytes transition.before.core.digest ++ [domAdvance] := by
  rcases transition with ⟨before, event, after⟩
  cases event with
  | proverC1 root => simp [squeezePairInputsOfTransition] at exactInputs
  | proverC2 lambda chi commitment =>
      simp [squeezePairInputsOfTransition] at exactInputs
  | proverPayload payload =>
      simp [squeezePairInputsOfTransition] at exactInputs
  | proverWorkNonce stage nonce =>
      simp [squeezePairInputsOfTransition] at exactInputs
  | verifier action reply =>
      cases action with
      | squeezePair owner block =>
          simp only [squeezePairInputsOfTransition, Option.some.injEq,
            Prod.mk.injEq] at exactInputs
          exact ⟨exactInputs.1.symm, exactInputs.2.symm⟩
      | absorb payload => simp [squeezePairInputsOfTransition] at exactInputs
      | requestRootSalt tree =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | absorbC1 root => simp [squeezePairInputsOfTransition] at exactInputs
      | absorbC2 lambda chi commitment =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | workProbe stage nonce kind =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | checkpoint checkpoint =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | markQ16Base => simp [squeezePairInputsOfTransition] at exactInputs
      | q16CandidateAbsorb counter outcome selected =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | q16Restore counter =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | q16Selected counter =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | q16SamplerAbortReject counter =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | q16AllNoncompactReject =>
          simp [squeezePairInputsOfTransition] at exactInputs
      | terminal => simp [squeezePairInputsOfTransition] at exactInputs

/-- The projected record list produced by a machine callback contains exactly
fresh records for its declared actor. -/
theorem only_machine_fresh_actor_projected_records
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    OnlyMachineFreshActor actor (projectedMachineFreshRecords actor queries) := by
  intro record member
  induction queries with
  | nil => simp [projectedMachineFreshRecords] at member
  | cons query rest ih =>
      rcases query with ⟨input, answer⟩
      simp only [projectedMachineFreshRecords, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨input, answer, rfl⟩
      · exact ih member

theorem projected_node_execution_pair_is_adjacent_in_full_trace
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullRun : SchedulerNativeRun Final}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final) startProgram environment
      configuration fullRun.trace accumulator child) :
    AdjacentScheduledPairInTrace execution.scheduled fullRun.trace := by
  refine ⟨execution.traceBeforePair,
    execution.proverRecords ++ execution.verifierRecords ++
      execution.traceAfterVerifier, ?_⟩
  simpa [List.append_assoc] using execution.fullTraceExact

theorem projected_node_execution_programming_uses_scheduled_coordinates
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullRun : SchedulerNativeRun Final}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final) startProgram environment
      configuration fullRun.trace accumulator child) :
    programConcretePair configuration.oracleLimits
        configuration.pairProgrammingOrder execution.prepared.programmingBase
        execution.prepared.outputInput execution.prepared.advanceInput
        execution.scheduled.forkOutput execution.scheduled.forkAdvance =
      .ready child.proverEntryOracle := by
  have coordinates :=
    scheduled_fork_coins_configuration_exact execution.scheduled
  simpa [coordinates.1, coordinates.2] using execution.programmingExact

theorem projected_node_execution_prover_answers_exact
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullRun : SchedulerNativeRun Final}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final) startProgram environment
      configuration fullRun.trace accumulator child) :
    machineFreshAnswers execution.proverRecords =
      execution.proverPrefix.freshQueries.map Prod.snd := by
  calc
    machineFreshAnswers execution.proverRecords =
        (machineFreshQueryAnswers execution.proverRecords).map Prod.snd :=
      machine_fresh_answers_eq_query_answers_map execution.proverRecords
    _ = execution.proverPrefix.freshQueries.map Prod.snd :=
      congrArg (List.map Prod.snd) execution.proverQueriesExact

theorem projected_node_execution_verifier_answers_exact
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullRun : SchedulerNativeRun Final}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final) startProgram environment
      configuration fullRun.trace accumulator child) :
    machineFreshAnswers execution.verifierRecords =
      execution.verifierPrefix.freshQueries.map Prod.snd := by
  calc
    machineFreshAnswers execution.verifierRecords =
        (machineFreshQueryAnswers execution.verifierRecords).map Prod.snd :=
      machine_fresh_answers_eq_query_answers_map execution.verifierRecords
    _ = execution.verifierPrefix.freshQueries.map Prod.snd :=
      congrArg (List.map Prod.snd) execution.verifierQueriesExact

/-- Successful descendant forks exclude the inherited transition at index
zero; repeated root forks remain permitted. -/
theorem projected_node_execution_nonroot_index_ne_zero
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullTrace : List UnifiedExposureRecord}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : CausallyProvenancedRestorationNodeExecution (Final := Final) startProgram environment
      configuration fullTrace accumulator child)
    (nonroot : execution.base.prepared.request.nodeId ≠ 0) :
    execution.base.prepared.request.verifierTransitionIndex ≠ 0 := by
  exact execution.requestIsStructurallyFresh.resolve_left nonroot

/-- Prefix preparation observes the accumulator only through the selected
node lookup.  This is the transport lemma needed when the append-only store
grows after an older child was certified. -/
theorem prepare_from_start_eq_of_node_lookup_eq
    {Statement Proof Payload : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (left right : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (selected : left.node? request.nodeId = right.node? request.nodeId) :
    prepareConcreteRestorationFromStartProgram startProgram configuration left
        request =
      prepareConcreteRestorationFromStartProgram startProgram configuration
        right request := by
  unfold prepareConcreteRestorationFromStartProgram
  rw [selected]

/-- Charges and failures cannot invalidate an existing preparation
certificate because neither operation changes the node store. -/
theorem prepare_from_start_add_charges_and_failure
    {Statement Proof Payload : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request failureRequest : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (charges : List ConcreteRestorationCharge) :
    prepareConcreteRestorationFromStartProgram startProgram configuration
        ((accumulator.addCharges charges).addFailure failureRequest reason)
        request =
      prepareConcreteRestorationFromStartProgram startProgram configuration
        accumulator request := by
  apply prepare_from_start_eq_of_node_lookup_eq
  rfl

/-- An already certified child remains certified when the append-only trace
and accumulator grow, provided the selected immutable parent lookup is
unchanged.  The old `traceAfterVerifier` simply absorbs the new suffix. -/
def transport_projected_restoration_node_execution
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (oldTrace newTrace suffix : List UnifiedExposureRecord)
    (oldAccumulator newAccumulator :
      ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload)
    (execution : ProjectedRestorationNodeExecution
      (Final := Final) startProgram environment configuration oldTrace
      oldAccumulator child)
    (traceExact : newTrace = oldTrace ++ suffix)
    (selectedExact :
      newAccumulator.node? execution.prepared.request.nodeId =
        oldAccumulator.node? execution.prepared.request.nodeId) :
    ProjectedRestorationNodeExecution
      (Final := Final) startProgram environment configuration newTrace
      newAccumulator child :=
  { prepared := execution.prepared
    preparationExact := by
      rw [prepare_from_start_eq_of_node_lookup_eq startProgram configuration
        newAccumulator oldAccumulator execution.prepared.request selectedExact]
      exact execution.preparationExact
    parentRequestExact := execution.parentRequestExact
    restoredEntryExact := execution.restoredEntryExact
    traceBeforePair := execution.traceBeforePair
    proverRecords := execution.proverRecords
    verifierRecords := execution.verifierRecords
    traceAfterVerifier := execution.traceAfterVerifier ++ suffix
    scheduled := execution.scheduled
    scheduledFrozenHistoryExact := execution.scheduledFrozenHistoryExact
    scheduledOutputInputExact := execution.scheduledOutputInputExact
    scheduledAdvanceInputExact := execution.scheduledAdvanceInputExact
    scheduledTemplateExact := execution.scheduledTemplateExact
    scheduledInputStateExact := execution.scheduledInputStateExact
    fullTraceExact := by
      calc
        newTrace = oldTrace ++ suffix := traceExact
        _ = (execution.traceBeforePair ++
              scheduledPairRecords execution.scheduled ++
              execution.proverRecords ++ execution.verifierRecords ++
              execution.traceAfterVerifier) ++ suffix :=
          congrArg (fun trace => trace ++ suffix) execution.fullTraceExact
        _ = execution.traceBeforePair ++
              scheduledPairRecords execution.scheduled ++
              execution.proverRecords ++ execution.verifierRecords ++
              (execution.traceAfterVerifier ++ suffix) := by
          simp [List.append_assoc]
    programmingExact := execution.programmingExact
    proverPrefix := execution.proverPrefix
    proverRecordsOnly := execution.proverRecordsOnly
    proverQueriesExact := execution.proverQueriesExact
    proverReturned := execution.proverReturned
    proverFinalExact := execution.proverFinalExact
    verifierEntryOracleExact := execution.verifierEntryOracleExact
    restoredBindingExact := execution.restoredBindingExact
    verifierPrefix := execution.verifierPrefix
    verifierRecordsOnly := execution.verifierRecordsOnly
    verifierQueriesExact := execution.verifierQueriesExact
    verifierReturned := execution.verifierReturned
    verifierFinalExact := execution.verifierFinalExact }

/-- Causal provenance transports along an append-only scheduler trace exactly
as the base execution does.  Earlier-pair witnesses remain in the unchanged
prefix; the positive-transition witness refers only to the node's own fixed
prover/verifier slices. -/
def transport_causally_provenanced_restoration_node_execution
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (oldTrace newTrace suffix : List UnifiedExposureRecord)
    (oldAccumulator newAccumulator :
      ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload)
    (execution : CausallyProvenancedRestorationNodeExecution
      (Final := Final) startProgram environment configuration oldTrace
      oldAccumulator child)
    (traceExact : newTrace = oldTrace ++ suffix)
    (selectedExact :
      newAccumulator.node? execution.base.prepared.request.nodeId =
        oldAccumulator.node? execution.base.prepared.request.nodeId) :
    CausallyProvenancedRestorationNodeExecution
      (Final := Final) startProgram environment configuration newTrace
      newAccumulator child :=
  { base := transport_projected_restoration_node_execution
      startProgram environment configuration oldTrace newTrace suffix
      oldAccumulator newAccumulator child execution.base traceExact selectedExact
    requestIsStructurallyFresh := execution.requestIsStructurallyFresh
    programmingHistoryHasEarlierPairProvenance :=
      execution.programmingHistoryHasEarlierPairProvenance
    positiveTransitionDigestProvenance :=
      execution.positiveTransitionDigestProvenance }

/-- Appending one node preserves every earlier indexed lookup. -/
theorem node_lookup_preserved_by_add_node
    {Statement Proof Payload : Type u}
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child parent : ConcreteRestorationNode Statement Proof Payload)
    (nodeId : Nat)
    (found : accumulator.node? nodeId = some parent) :
    (accumulator.addNode child).2.node? nodeId = some parent := by
  unfold ConcreteRestorationAccumulator.node? at found ⊢
  rw [List.getElem?_eq_some_iff] at found
  rcases found with ⟨within, valueExact⟩
  rw [ConcreteRestorationAccumulator.addNode,
    List.getElem?_append_left within, List.getElem?_eq_some_iff]
  exact ⟨within, valueExact⟩

/-- Any proof-free accumulator update that leaves the node list literally
unchanged transports all node certificates.  This is the common lemma behind
charge and failure bookkeeping. -/
theorem every_node_operational_of_nodes_eq
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace suffix : List UnifiedExposureRecord)
    (oldAccumulator newAccumulator :
      ConcreteRestorationAccumulator Statement Proof Payload)
    (nodesExact : newAccumulator.nodes = oldAccumulator.nodes)
    (invariant : EveryNodeOperational (Final := Final) startProgram environment
      configuration trace oldAccumulator) :
    EveryNodeOperational (Final := Final) startProgram environment configuration
      (trace ++ suffix) newAccumulator := by
  intro child member parentRequest
  have oldMember : child ∈ oldAccumulator.nodes := by
    rw [← nodesExact]
    exact member
  obtain ⟨execution⟩ := invariant child oldMember parentRequest
  refine ⟨transport_projected_restoration_node_execution startProgram
    environment configuration trace (trace ++ suffix) suffix oldAccumulator
    newAccumulator child execution rfl ?_⟩
  unfold ConcreteRestorationAccumulator.node?
  rw [nodesExact]

/-- Charges change no node lookup and therefore transport every prior
operational certificate along any exact scheduler-trace suffix. -/
theorem every_node_operational_add_charges
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace suffix : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge)
    (invariant : EveryNodeOperational (Final := Final) startProgram environment
      configuration trace accumulator) :
    EveryNodeOperational (Final := Final) startProgram environment configuration
      (trace ++ suffix) (accumulator.addCharges charges) := by
  exact every_node_operational_of_nodes_eq startProgram environment configuration
    trace suffix accumulator (accumulator.addCharges charges) rfl invariant

/-- Failure logging changes no node lookup and therefore transports every prior
operational certificate along any exact scheduler-trace suffix. -/
theorem every_node_operational_add_failure
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace suffix : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (invariant : EveryNodeOperational (Final := Final) startProgram environment
      configuration trace accumulator) :
    EveryNodeOperational (Final := Final) startProgram environment configuration
      (trace ++ suffix) (accumulator.addFailure request reason) := by
  exact every_node_operational_of_nodes_eq startProgram environment configuration
    trace suffix accumulator (accumulator.addFailure request reason) rfl invariant

/-- Append one freshly certified node while transporting every earlier
certificate through the append-only store and scheduler trace. -/
theorem every_node_operational_add_certified_node
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace suffix : List UnifiedExposureRecord)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (child : ConcreteRestorationNode Statement Proof Payload)
    (invariant : EveryNodeOperational (Final := Final) startProgram environment
      configuration trace accumulator)
    (childExecution : ProjectedRestorationNodeExecution
      (Final := Final) startProgram environment configuration (trace ++ suffix)
      (accumulator.addNode child).2 child) :
    EveryNodeOperational (Final := Final) startProgram environment configuration
      (trace ++ suffix) (accumulator.addNode child).2 := by
  intro candidate member parentRequest
  have memberCases : candidate ∈ accumulator.nodes ∨ candidate = child := by
    simpa [ConcreteRestorationAccumulator.addNode] using member
  rcases memberCases with oldMember | candidateExact
  · obtain ⟨execution⟩ := invariant candidate oldMember parentRequest
    have selectedSome : ∃ parent,
        accumulator.node? execution.prepared.request.nodeId = some parent := by
      cases selected : accumulator.node? execution.prepared.request.nodeId with
      | none =>
          have impossible := execution.preparationExact
          simp [prepareConcreteRestorationFromStartProgram, selected] at impossible
      | some parent => exact ⟨parent, rfl⟩
    refine ⟨transport_projected_restoration_node_execution startProgram
      environment configuration trace (trace ++ suffix) suffix accumulator
      (accumulator.addNode child).2 candidate execution rfl ?_⟩
    rcases selectedSome with ⟨parent, selected⟩
    rw [selected]
    exact node_lookup_preserved_by_add_node accumulator child parent
      execution.prepared.request.nodeId selected
  · subst candidate
    exact ⟨childExecution⟩

/-- The singleton root contains no nonroot child, independently of the trace
prefix accumulated by the two initial machine stages. -/
theorem initial_every_node_operational
    {Statement Proof Payload Final : Type u}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (trace : List UnifiedExposureRecord)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (rootIsRoot : root.parentRequest = none) :
    EveryNodeOperational (Final := Final) startProgram environment configuration
      trace (initialRestorationAccumulatorFromRoot root) := by
  intro child member parentRequest
  have childExact : child = root := by
    simpa [initialRestorationAccumulatorFromRoot] using member
  subst child
  exact (parentRequest rootIsRoot).elim

#print axioms prepare_from_start_eq_of_node_lookup_eq
#print axioms prepare_from_start_add_charges_and_failure
#print axioms transport_projected_restoration_node_execution
#print axioms transport_causally_provenanced_restoration_node_execution
#print axioms initial_every_node_operational
#print axioms projected_node_execution_pair_is_adjacent_in_full_trace
#print axioms projected_node_execution_programming_uses_scheduled_coordinates
#print axioms projected_node_execution_prover_answers_exact
#print axioms projected_node_execution_verifier_answers_exact
#print axioms projected_node_execution_nonroot_index_ne_zero

end

end AspisK1.V7Tag73OperationalNodeCertificate
