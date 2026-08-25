import AspisFormal.K1.V7Tag73ConcreteStateRestoration
import AspisFormal.K1.V7FsStateRestorationCoupling

/-!
# Alignment of generic start-only replay with a generated Tag-73 fork

`CoupledReplay` deliberately stores an untyped SHA query.  Therefore an
arbitrary generic replay cannot be decoded into a Tag-73 phase: the deployed
squeeze input `S || 0x01` contains neither its owner nor its block number.

The non-circular direction is the one used by an extractor.  It first chooses
an actual `GeneratedReplayPrefix` from the concrete query DAG, computes the
corresponding squeeze-output input from the successful concrete first
execution, and gives that input to the generic start-only replay algorithm.
If that algorithm succeeds, its real Q1 split is at exactly the requested
input.  Separately, the chosen DAG prefix has a unique complete,
previously-seen verifier snapshot.  Input equality alone does not prove that
the replayed Q1 prefix is the generated schedule/history prefix: the same
`S || 0x01` address can recur after a state collision, and the address erases
the squeeze owner and block.

This module proves that direction and separately proves the input-only
non-injectivity obstruction.  It does not posit a trace-cover relation, a
restore function, or a decoder from arbitrary byte strings to protocol phases.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CoupledReplayAlignment

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73DagActionAlignment
open AspisK1.V7Tag73ConcreteStateRestoration
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

/-! ## One table representation shared with the generic first run -/

/-- Forget only the experiment-specific table-source tag.  Inputs, outputs,
and insertion order are retained exactly. -/
def fixedTableOfOracleState (state : OracleState) : FixedOracleTable :=
  state.table.map fun entry =>
    ({ input := entry.input, output := entry.output } :
      AspisK1.V7Tag73DeterministicRefinement.TableEntry)

@[simp] theorem fixed_table_of_oracle_state_length (state : OracleState) :
    (fixedTableOfOracleState state).length = state.table.length := by
  simp [fixedTableOfOracleState]

/-! ## A generated replay request -/

/-- The first query of the next atomic squeeze action, computed from the
complete first-run snapshot at the generated checkpoint. -/
noncomputable def generatedDrivingInput
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) : ShaInput :=
  let restoration := concreteRestoration execution generated
  bytes restoration.snapshot.core.digest ++ [domSqueeze]

theorem generated_driving_input_is_exact_next_squeeze_output_input
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    let restoration := concreteRestoration execution generated
    actionInputs restoration.snapshot.bindings restoration.snapshot.core
        (.squeezePair restoration.checkpoint.owner
          restoration.checkpoint.block) =
      [generatedDrivingInput execution generated,
       bytes restoration.snapshot.core.digest ++ [domAdvance]] := by
  have paired :=
    (restoration_squeeze_is_one_atomic_two_query_action
      (concreteRestoration execution generated)).2.1
  simpa [generatedDrivingInput, domSqueeze, domAdvance] using paired

/-- Specialize only the driving input of an otherwise fixed replay
configuration.  The prefix is data from the DAG, not a conclusion returned by
the generic coupling. -/
noncomputable def configurationForGeneratedReplay
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : OriginReplayConfiguration) :
    OriginReplayConfiguration :=
  { configuration with
    transcriptDrivingInput := generatedDrivingInput execution generated }

@[simp] theorem configuration_for_generated_driving_input
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : OriginReplayConfiguration) :
    (configurationForGeneratedReplay execution generated configuration).transcriptDrivingInput =
      generatedDrivingInput execution generated := by
  rfl

@[simp] theorem configuration_for_generated_preserves_replay_fuel
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : OriginReplayConfiguration) :
    (configurationForGeneratedReplay execution generated configuration).replayFuel =
      configuration.replayFuel := by
  rfl

@[simp] theorem configuration_for_generated_preserves_budget
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : OriginReplayConfiguration) :
    (configurationForGeneratedReplay execution generated configuration).budget =
      configuration.budget := by
  rfl

/-! ## Actual Q1/pause alignment on successful generic replay -/

theorem successful_generated_replay_splits_actual_q1_at_exact_input
    {TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (execution : ConcreteFirstExecution
      (fixedTableOfOracleState origin.firstRun.stateAtAdversaryHalt) dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : OriginReplayConfiguration)
    (output :
      {run : CoupledReplay TapeIdentity Statement Proof Result //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (configurationForGeneratedReplay execution generated configuration))
          run})
    (success : constructLegalReplayFromOrigin? origin
      (configurationForGeneratedReplay execution generated configuration) =
        some output) :
    output.1.q1 = origin.firstRun.q1 ∧
      output.1.q1 =
        output.1.replayPrefix ++ output.1.driving :: output.1.suffix ∧
      output.1.driving.input = generatedDrivingInput execution generated ∧
      0 < output.1.replayPrefix.length ∧
      output.1.prefixRun.halt = .paused output.1.residualProgram ∧
      queryAnswerTrace
          (historySince origin.initialOracle output.1.prefixRun.oracle) =
        queryAnswerTrace output.1.replayPrefix := by
  have genericSuccess :
      constructLegalReplay? origin.capability
        (fixedFirstRunRecordFromOrigin origin
          (configurationForGeneratedReplay execution generated configuration)) =
        some output := by
    simpa only [constructLegalReplayFromOrigin_unfold] using success
  have operational := map_success_is_operational origin.capability
    (fixedFirstRunRecordFromOrigin origin
      (configurationForGeneratedReplay execution generated configuration))
    output genericSuccess
  rcases operational with
    ⟨_, _, q1, decomposition, driving, nonempty, _, _, paused, trace,
      _, _, _, _, _, _, _, _⟩
  refine ⟨?_, decomposition, ?_, nonempty, paused, ?_⟩
  · simpa using q1
  · simpa only [fixedFirstRunRecordFromOrigin_transcriptDrivingInput,
      configuration_for_generated_driving_input] using driving
  · simpa using trace

/-- Pairing with the concrete state map.  The generic replay contributes the
actual Q1 split and raw pause-input equality; all completeness and
previously-seen facts are derived independently from the successful first
execution.  This theorem deliberately does not identify the replayed history
with `replayLocation generated`. -/
theorem successful_generated_replay_pairs_with_unique_complete_restoration
    {TapeIdentity Observation Statement Proof Result : Type*}
    {dag : ConcreteDagInstance}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Result)
    (execution : ConcreteFirstExecution
      (fixedTableOfOracleState origin.firstRun.stateAtAdversaryHalt) dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : OriginReplayConfiguration)
    (output :
      {run : CoupledReplay TapeIdentity Statement Proof Result //
        IsOperationalCoupling origin.capability
          (fixedFirstRunRecordFromOrigin origin
            (configurationForGeneratedReplay execution generated configuration))
          run})
    (success : constructLegalReplayFromOrigin? origin
      (configurationForGeneratedReplay execution generated configuration) =
        some output) :
    let restoration := concreteRestoration execution generated
    output.1.driving.input = generatedDrivingInput execution generated ∧
      (fullPlan dag.tape).get restoration.actionCursor =
        .squeezePair restoration.checkpoint.owner
          restoration.checkpoint.block ∧
      IsComplete restoration.snapshot ∧
      PreviouslySeen restoration.snapshot
        restoration.sourceExecution.interactiveState ∧
      NonemptyVerifierHistory
        restoration.sourceExecution.interactiveState ∧
      restoration.snapshot.bindings =
        FixedBindings.ofContext dag.tape.messages.context ∧
      restoration.oracleTable =
        fixedTableOfOracleState origin.firstRun.stateAtAdversaryHalt ∧
      restoration.deployedTape = dag.tape ∧
      ∃! concrete : ConcreteRestorationRecord
          (fixedTableOfOracleState origin.firstRun.stateAtAdversaryHalt) dag,
        IsConcreteRestorationOf execution generated concrete := by
  have split := successful_generated_replay_splits_actual_q1_at_exact_input
    origin execution generated configuration output success
  let restoration := concreteRestoration execution generated
  exact ⟨split.2.2.1,
    restoration_next_action_is_exact_squeeze_pair restoration,
    restoration_snapshot_is_complete restoration,
    restoration_snapshot_is_previously_seen restoration,
    restoration_first_run_history_is_nonempty restoration,
    restoration_preserves_fixed_bindings restoration,
    restoration_retains_same_oracle_table restoration,
    restoration_retains_same_deployed_tape restoration,
    concrete_restoration_exists_unique execution generated⟩

/-!
The remaining deterministic bridge is an executable schedule/history matcher:
it must label the actual ordered adversary query records with the concrete
Tag-73 roles (while allowing other adversary SHA calls), prove that the labels
follow `replayLocation generated`, and rule out an earlier equal `S || 0x01`
address except through a named collision event.  Neither `CoupledReplay` nor
`QueryRecord` currently contains those labels.  The following theorems show
why a reverse decoder from the raw pause input cannot replace that matcher.
-/

/-! ## Exact obstruction to reverse decoding from a generic pause -/

def untypedSqueezeOutputInput (state : Digest256)
    (tag : SqueezeOwner × Nat) : ShaInput :=
  (RawQueryRole.squeezeOutput tag.1 tag.2).input state

theorem untyped_squeeze_output_input_erases_owner_and_block
    (state : Digest256) (tag : SqueezeOwner × Nat) :
    untypedSqueezeOutputInput state tag =
      bytes state ++ [domSqueeze] := by
  rfl

theorem untyped_squeeze_output_input_is_not_injective
    (state : Digest256) :
    ¬ Function.Injective (untypedSqueezeOutputInput state) := by
  intro injective
  let owner : SqueezeOwner := .challenge .theta
  have equalInputs :
      untypedSqueezeOutputInput state (owner, 0) =
        untypedSqueezeOutputInput state (owner, 1) := by
    rfl
  have equalTags := injective equalInputs
  have equalBlocks := congrArg Prod.snd equalTags
  omega

/-- No decoder seeing only the generic pause input can recover owner and block
for every possible Tag-73 squeeze label, even when the transcript state is
fixed and known. -/
theorem no_total_owner_block_decoder_from_untyped_pause_input
    (state : Digest256) :
    ¬ ∃ decode : ShaInput → SqueezeOwner × Nat,
      ∀ tag : SqueezeOwner × Nat,
        decode (untypedSqueezeOutputInput state tag) = tag := by
  rintro ⟨decode, correct⟩
  let owner : SqueezeOwner := .challenge .theta
  have first := correct (owner, 0)
  have second := correct (owner, 1)
  have equalInputs :
      untypedSqueezeOutputInput state (owner, 0) =
        untypedSqueezeOutputInput state (owner, 1) := by
    rfl
  rw [equalInputs] at first
  have equalTags : (owner, 0) = (owner, 1) := first.symm.trans second
  have equalBlocks := congrArg Prod.snd equalTags
  omega

def untypedSqueezeQueryRecord (state output : Digest256)
    (tag : SqueezeOwner × Nat) : QueryRecord where
  input := untypedSqueezeOutputInput state tag
  output := output
  actor := .adversary
  origin := .cached

theorem untyped_squeeze_query_record_is_not_injective
    (state output : Digest256) :
    ¬ Function.Injective (untypedSqueezeQueryRecord state output) := by
  intro injective
  let owner : SqueezeOwner := .challenge .theta
  have equalRecords :
      untypedSqueezeQueryRecord state output (owner, 0) =
        untypedSqueezeQueryRecord state output (owner, 1) := by
    rfl
  have equalTags := injective equalRecords
  have equalBlocks := congrArg Prod.snd equalTags
  omega

#print axioms fixed_table_of_oracle_state_length
#print axioms generated_driving_input_is_exact_next_squeeze_output_input
#print axioms configuration_for_generated_driving_input
#print axioms successful_generated_replay_splits_actual_q1_at_exact_input
#print axioms successful_generated_replay_pairs_with_unique_complete_restoration
#print axioms untyped_squeeze_output_input_erases_owner_and_block
#print axioms untyped_squeeze_output_input_is_not_injective
#print axioms no_total_owner_block_decoder_from_untyped_pause_input
#print axioms untyped_squeeze_query_record_is_not_injective

end AspisK1.V7Tag73CoupledReplayAlignment
