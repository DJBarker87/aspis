import AspisFormal.K1.V7Tag73K12Merkle208PrefixProjection
import AspisFormal.K1.V7Tag73ExactFixedK12PrefixClassifier
import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal
import AspisFormal.K1.V7Tag73CompletedRootProjection
import AspisFormal.K1.V7Tag73FullResultRootRuns
import AspisFormal.K1.V7Tag73VerifierOracleStability
import AspisFormal.K1.V7Tag73ActualNodeCausalProvenance
import AspisFormal.K1.V7Tag73FullCursorClientLineageLift
import AspisFormal.Pool.V7MerklePartialPathExtractor
import AspisFormal.Pool.V7MerklePrefixTargetCongruence
import AspisFormal.Pool.V7MerkleFirstUnresolvedBinding

/-!
# Full-output budgeted scheduler tree for exact Tag-73 K1.2

This module constructs the causal object needed by the K1.2 probability
bridge.  The tree follows the literal result-carrying root scheduler and
branches on complete 256-bit answers.  Prover coordinates are free.  Once the
same-tape prover has returned, root-verifier coordinates are charged against
its fuel budget and test the full-output preimage of the at-most-32
first-unresolved Merkle targets.

The target set is recomputed from the executable prover run on the answer
prefix already exposed.  It therefore cannot inspect the current or a future
answer.  The remaining work is the deterministic inclusion from a concrete
late target hit in a completed exact K1.2 input into this tree event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K12BudgetedSchedulerTree

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7BudgetedAdaptiveTargets
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73FullResultRootRuns
open AspisK1.V7Tag73RootSuccessForcesFullCompletion
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73K12Merkle208CollisionProbability
open AspisK1.V7Tag73K12Merkle208PrefixProjection
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerklePartialPathExtractor
open AspisPool.V7MerklePrefixTargetCongruence
open AspisPool.V7MerkleFirstUnresolvedBinding

noncomputable section

abbrev K12RuntimeTargetCap : Nat :=
  prefixFixedResolutionTargetCap * 2 ^ 48

/-- Definitionally recursive constant cap vector.  Using this form keeps
single-step dependent reductions transparent to Lean's kernel. -/
def k12RuntimeCaps : Nat → List Nat
  | 0 => []
  | remaining + 1 => K12RuntimeTargetCap :: k12RuntimeCaps remaining

@[simp] theorem k12_runtime_caps_succ (remaining : Nat) :
    k12RuntimeCaps (remaining + 1) =
      K12RuntimeTargetCap :: k12RuntimeCaps remaining := by
  rfl

@[simp] theorem k12_runtime_caps_length (remaining : Nat) :
    (k12RuntimeCaps remaining).length = remaining := by
  induction remaining with
  | zero => rfl
  | succ remaining ih => simp [k12RuntimeCaps, ih]

/-- Definition-preserving presentation of an exact compiler tape at the
recursive cap vector's propositionally equal length. -/
def k12RuntimeTape {Output : Type} :
    ∀ {remaining : Nat}, FreshAnswerTape Output remaining →
      FreshAnswerTape Output (k12RuntimeCaps remaining).length
  | 0, tape => tape
  | remaining + 1, tape =>
      (tape.1, k12RuntimeTape tape.2)

@[simp] theorem fresh_answer_k12_runtime_tape_to_list
    {Output : Type} {remaining : Nat}
    (tape : FreshAnswerTape Output remaining) :
    freshAnswerTapeToList (k12RuntimeTape tape) =
      freshAnswerTapeToList tape := by
  induction remaining with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      change tape.1 :: freshAnswerTapeToList (k12RuntimeTape tape.2) =
        tape.1 :: freshAnswerTapeToList tape.2
      rw [inductionHypothesis]

/-- The 208-bit table view determined by one already-reached oracle state. -/
def truncateAtOracleState (state : OracleState) :
    RawHashInput → MerkleDigest208 :=
  fun rawInput =>
    match lookupEntry state (rawHashInputToRuntimeInput rawInput) with
    | some entry => runtimeDigest256PrefixToMerkleDigest entry.output
    | none => zeroMerkleDigest

def rootsOfReturnedValue
    {Statement Payload : Type}
    (value : CheckedRawTag73AdversaryReturnedValue Statement
      Tag73K12ParsedProof Payload) : Roots :=
  { c1 := runtimeDigest208ToMerkleDigest value.rawMessages.c1Root
    c2 := runtimeDigest208ToMerkleDigest value.rawMessages.c2Root }

def openingsOfReturnedValue
    {Statement Payload : Type}
    (value : CheckedRawTag73AdversaryReturnedValue Statement
      Tag73K12ParsedProof Payload) : TwoTreeOpeningProof :=
  value.1.publicProof.proof.rawProof.openings

/-- Literal same-hidden-tape prover execution under a finite exposed-answer
prefix.  Extra answers after prover return are ignored by `runMachine`. -/
def k12ProverRunFromAnswerPrefix
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (answers : List Digest256) :
    MachineRun
      (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
        Payload) :=
  runMachine
    (controllerFromProjectedFreshAnswers emptyOracle.history answers)
    machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
    (machine.blackBox.start hidden machine.observation)

/-- The exact prefix-measurable target set.  There is no target before the
prover returns normally. -/
def k12PrefixTargetsFromAnswers
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (answers : List Digest256) :
    Finset MerkleDigest208 :=
  let run := k12ProverRunFromAnswerPrefix machine hidden answers
  match run.halt with
  | .returned value =>
      prefixResolutionTargetSet (truncateAtOracleState run.oracle)
        (run.oracle.history.map
          (fun record : QueryRecord =>
            runtimeInputToRawHashInput record.input))
        (rootsOfReturnedValue value) (openingsOfReturnedValue value)
  | .oracleAbort _ | .outOfFuel => ∅

theorem k12_prefix_targets_from_answers_card_le
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (answers : List Digest256) :
    (k12PrefixTargetsFromAnswers machine hidden answers).card ≤
      prefixFixedResolutionTargetCap := by
  change (match (k12ProverRunFromAnswerPrefix machine hidden answers).halt with
    | .returned value =>
        prefixResolutionTargetSet
          (truncateAtOracleState
            (k12ProverRunFromAnswerPrefix machine hidden answers).oracle)
          ((k12ProverRunFromAnswerPrefix machine hidden answers).oracle.history.map
            (fun record : QueryRecord =>
              runtimeInputToRawHashInput record.input))
          (rootsOfReturnedValue value) (openingsOfReturnedValue value)
    | .oracleAbort _ | .outOfFuel => ∅).card ≤ _
  generalize haltEq :
    (k12ProverRunFromAnswerPrefix machine hidden answers).halt = halt
  cases halt with
  | returned value =>
      simpa [prefixFixedResolutionTargetCap] using
      prefixResolutionTargetSet_card_le
        (truncateAtOracleState
          (k12ProverRunFromAnswerPrefix machine hidden answers).oracle)
        ((k12ProverRunFromAnswerPrefix machine hidden answers).oracle.history.map
          (fun record : QueryRecord =>
            runtimeInputToRawHashInput record.input))
        (rootsOfReturnedValue _)
        (openingsOfReturnedValue _)
  | oracleAbort reason => simp
  | outOfFuel => simp

theorem k12_runtime_targets_from_answers_card_le
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (answers : List Digest256) :
    (deployedPrefixTargetPreimage
        (k12PrefixTargetsFromAnswers machine hidden answers)).card ≤
      K12RuntimeTargetCap := by
  exact deployed_prefix_target_preimage_card_le _
    (k12_prefix_targets_from_answers_card_le machine hidden answers)

/-! ## Returned prover prefixes ignore later verifier coordinates -/

/-- A proof-relevant returned fresh trace still returns identically when an
arbitrary answer tail is present.  The machine halts before consulting it. -/
theorem projected_fresh_returned_trace_interpreter_append_exact
    {MachineResult : Type}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState)
    (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256))
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (coherent : HistoryTotalCoherent state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) (tail : List Digest256) :
    runProjectedFreshSegment limits actor
        (freshQueries.map Prod.snd ++ tail) fuel state program coherent =
      { halt := .returned result, oracle := finalState, steps := steps } := by
  induction trace with
  | returned fuel state program traceCoherent result finalState steps sought =>
      rw [runProjectedFreshSegment, sought]
  | fresh fuel state requestState program traceCoherent input next
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought answer rest result finalState tailSteps restTrace ih =>
      simp only [List.map_cons, List.cons_append]
      rw [runProjectedFreshSegment, sought]
      change addMachineRunSteps
          (runProjectedFreshSegment limits actor
            (rest.map Prod.snd ++ tail) remainingFuel
            (freshQueryState actor requestState input answer) (next answer)
            (fresh_query_state_preserves_history_total_coherent actor
              requestState input answer requestCoherent))
          (cachedSteps + 1) =
        { halt := .returned result
          oracle := finalState
          steps := tailSteps + (cachedSteps + 1) }
      rw [ih]
      rfl

/-- The same theorem for the ordinary controller reconstructed from the
consumed prefix plus an arbitrary untouched suffix. -/
theorem projected_fresh_returned_trace_run_machine_append_exact
    {MachineResult : Type}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState)
    (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256))
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (coherent : HistoryTotalCoherent state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) (tail : List Digest256) :
    runMachine
        (controllerFromProjectedFreshAnswers state.history
          (freshQueries.map Prod.snd ++ tail))
        limits actor fuel state program =
      { halt := .returned result, oracle := finalState, steps := steps } := by
  calc
    runMachine
        (controllerFromProjectedFreshAnswers state.history
          (freshQueries.map Prod.snd ++ tail))
        limits actor fuel state program =
      runProjectedFreshSegment limits actor
        (freshQueries.map Prod.snd ++ tail) fuel state program coherent := by
          symm
          simpa only [List.nil_append] using
            (run_projected_fresh_segment_eq_run_machine limits actor
              state.history [] (freshQueries.map Prod.snd ++ tail) fuel state
              program coherent (projected_fresh_suffix_initial state))
    _ = { halt := .returned result, oracle := finalState, steps := steps } :=
      projected_fresh_returned_trace_interpreter_append_exact limits actor
        fuel state program freshQueries result finalState steps coherent trace
          tail

/-- Once the exact prover segment has returned, replaying it from the literal
answer prefix yields the same raw adversary value and prover-final oracle,
regardless of how many already-exposed verifier answers follow. -/
theorem k12_prover_run_from_completed_prefix_append_exact
    {HiddenTape TapeIdentity Observation Statement Payload Final : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Tag73K12ParsedProof Payload)
    (prefixes : FullResultRootProjectedPrefixes (Final := Final) machine hidden
      available runtime)
    (tail : List Digest256) :
    k12ProverRunFromAnswerPrefix machine hidden
        (prefixes.adversary.freshQueries.map Prod.snd ++ tail) =
      { halt := .returned prefixes.adversaryValue
        oracle := prefixes.adversary.finalState
        steps := prefixes.adversary.steps } := by
  let controller := controllerFromProjectedFreshAnswers emptyOracle.history
    (prefixes.adversary.freshQueries.map Prod.snd ++ tail)
  have wrapped := projected_fresh_returned_trace_run_machine_append_exact
    machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
    (schedulerStageProgram
      Final
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation)))
    prefixes.adversary.freshQueries prefixes.adversary.result
    prefixes.adversary.finalState prefixes.adversary.steps
    empty_oracle_history_total_coherent prefixes.adversary.trace tail
  rw [prefixes.adversaryResult] at wrapped
  have totalized := run_machine_scheduler_stage_completed_reflects
    (Final := Final)
    controller machine.adversaryLimits .adversary machine.adversaryFuel
    emptyOracle
    (totalizeOracleMachine machine.adversaryFuel
      (machine.blackBox.start hidden machine.observation))
    (Except.ok prefixes.adversaryValue) prefixes.adversary.finalState
    prefixes.adversary.steps wrapped
  have raw := run_machine_totalized_ok_reflects controller
    machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
    (machine.blackBox.start hidden machine.observation)
    prefixes.adversaryValue prefixes.adversary.finalState
    prefixes.adversary.steps totalized
  simpa [k12ProverRunFromAnswerPrefix, controller] using raw

theorem k12_prefix_targets_stable_after_completed_prover
    {HiddenTape TapeIdentity Observation Statement Payload Final : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Tag73K12ParsedProof Payload)
    (prefixes : FullResultRootProjectedPrefixes (Final := Final) machine hidden
      available runtime)
    (tail : List Digest256) :
    k12PrefixTargetsFromAnswers machine hidden
        (prefixes.adversary.freshQueries.map Prod.snd ++ tail) =
      prefixResolutionTargetSet
        (truncateAtOracleState prefixes.adversary.finalState)
        (prefixes.adversary.finalState.history.map
          (fun record : QueryRecord =>
            runtimeInputToRawHashInput record.input))
        (rootsOfReturnedValue prefixes.adversaryValue)
        (openingsOfReturnedValue prefixes.adversaryValue) := by
  unfold k12PrefixTargetsFromAnswers
  rw [k12_prover_run_from_completed_prefix_append_exact machine hidden
    available runtime prefixes tail]

/-! ## Prover-table answers remain fixed through the root verifier -/

theorem projected_machine_prefix_table_extension
    {MachineResult : Type}
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine MachineResult)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    ∃ suffix, returned.finalState.table = state.table ++ suffix := by
  have coherent : HistoryTotalCoherent state :=
    projected_returned_trace_entry_coherent limits actor fuel state program
      returned.freshQueries returned.result returned.finalState returned.steps
        returned.trace
  have runExact := projected_machine_prefix_returned_run_exact limits actor
    fuel state program available returned coherent
  obtain ⟨appended, _history, table, _properties, _length⟩ :=
    run_machine_fresh_extension_data
      (controllerFromProjectedFreshAnswers state.history
        (returned.freshQueries.map Prod.snd))
      limits actor fuel state program
  rw [runExact] at table
  exact ⟨
    (appended.filter fun record => record.origin = .fresh).map
      freshTableEntryOfRecord,
    table⟩

theorem projected_machine_prefix_lookup_retains_segment_answer
    {MachineResult : Type}
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine MachineResult)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) (record : QueryRecord)
    (recordMember : record ∈ historySince state returned.finalState) :
    (lookupEntry returned.finalState record.input).map
        AspisK1.V7FsAokExperiment.TableEntry.output =
      some record.output := by
  have coherent : HistoryTotalCoherent state :=
    projected_returned_trace_entry_coherent limits actor fuel state program
      returned.freshQueries returned.result returned.finalState returned.steps
        returned.trace
  have runExact := projected_machine_prefix_returned_run_exact limits actor
    fuel state program available returned coherent
  have returnedHalt :
      (runMachine
        (controllerFromProjectedFreshAnswers state.history
          (returned.freshQueries.map Prod.snd))
        limits actor fuel state program).halt = .returned returned.result := by
    rw [runExact]
  obtain ⟨pairs, _path, traceExact, _actors, tableAnswers⟩ :=
    run_machine_returned_has_exact_query_path
      (controllerFromProjectedFreshAnswers state.history
        (returned.freshQueries.map Prod.snd))
      limits actor fuel state program returned.result returnedHalt
  have finalOracleExact :
      (runMachine
        (controllerFromProjectedFreshAnswers state.history
          (returned.freshQueries.map Prod.snd))
        limits actor fuel state program).oracle = returned.finalState := by
    rw [runExact]
  rw [finalOracleExact] at traceExact tableAnswers
  have pairMember : (record.input, record.output) ∈ pairs := by
    rw [← traceExact]
    exact List.mem_map.mpr ⟨record, recordMember, rfl⟩
  have found := tableAnswers (record.input, record.output) pairMember
  simpa only [fixed_table_lookup_eq_lookup_entry_output] using found

theorem table_find_append_preserves_some
    (table suffix : List AspisK1.V7FsAokExperiment.TableEntry)
    (input : ShaInput) (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (found : table.find? (fun candidate => candidate.input = input) =
      some entry) :
    (table ++ suffix).find? (fun candidate => candidate.input = input) =
      some entry := by
  induction table with
  | nil => simp at found
  | cons head tail ih =>
      by_cases hit : head.input = input
      · simpa [hit] using found
      · have tailFound :
            tail.find? (fun candidate => candidate.input = input) =
              some entry := by
          simpa [hit] using found
        simpa [hit] using ih tailFound

theorem lookupEntry_preserved_by_table_extension
    (before after : OracleState)
    (suffix : List AspisK1.V7FsAokExperiment.TableEntry)
    (extension : after.table = before.table ++ suffix)
    (input : ShaInput) (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (found : lookupEntry before input = some entry) :
    lookupEntry after input = some entry := by
  unfold lookupEntry at found ⊢
  rw [extension]
  exact table_find_append_preserves_some before.table suffix input entry found

/-- A lookup first found after an append-only table extension belongs to the
new suffix when it was absent from the entry table. -/
theorem lookupEntry_new_suffix_member
    (before after : OracleState)
    (suffix : List AspisK1.V7FsAokExperiment.TableEntry)
    (extension : after.table = before.table ++ suffix)
    (input : ShaInput) (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (missing : lookupEntry before input = none)
    (found : lookupEntry after input = some entry) :
    entry ∈ after.table.drop before.table.length := by
  have missing' : before.table.find?
      (fun candidate => candidate.input = input) = none := by
    simpa [lookupEntry] using missing
  have found' : (before.table ++ suffix).find?
      (fun candidate => candidate.input = input) = some entry := by
    simpa [lookupEntry, extension] using found
  rw [List.find?_append, missing'] at found'
  have suffixMember : entry ∈ suffix := List.mem_of_find?_eq_some found'
  rw [extension]
  simpa using suffixMember

theorem completed_root_truncate_views_agree_on_prover_history
    {HiddenTape TapeIdentity Observation Statement Payload Final : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Tag73K12ParsedProof Payload)
    (prefixes : FullResultRootProjectedPrefixes (Final := Final) machine hidden
      available runtime) :
    ∀ rawInput ∈ prefixes.adversary.finalState.history.map
        (fun record : QueryRecord =>
          runtimeInputToRawHashInput record.input),
      truncateAtOracleState prefixes.adversary.finalState rawInput =
        truncateAtOracleState prefixes.verifier.finalState rawInput := by
  obtain ⟨suffix, tableExtension⟩ :=
    projected_machine_prefix_table_extension machine.verifierLimits .verifier
      machine.verifierFuel prefixes.adversary.finalState
      (schedulerStageProgram
        Final
        (totalizeOracleMachine machine.verifierFuel
          (initialRawFutureFreeProgram machine.environment
            prefixes.adversaryValue.rawMessages machine.driverFuel)))
      prefixes.adversary.remaining prefixes.verifier
  intro rawInput rawMember
  obtain ⟨record, recordMember, rfl⟩ := List.mem_map.mp rawMember
  have segmentMember : record ∈
      historySince emptyOracle prefixes.adversary.finalState := by
    simpa [historySince, emptyOracle] using recordMember
  have retained := projected_machine_prefix_lookup_retains_segment_answer
    machine.adversaryLimits .adversary machine.adversaryFuel emptyOracle
    (schedulerStageProgram
      Final
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation)))
    available prefixes.adversary record segmentMember
  cases beforeLookup : lookupEntry prefixes.adversary.finalState record.input with
  | none => simp [beforeLookup] at retained
  | some entry =>
      have afterLookup := lookupEntry_preserved_by_table_extension
        prefixes.adversary.finalState prefixes.verifier.finalState suffix
        tableExtension record.input entry beforeLookup
      simp [truncateAtOracleState, rawHashInputToRuntimeInput_roundtrip,
        beforeLookup, afterLookup]

/-- The operational tree's prefix-measurable target set is exactly the target
set appearing in the fixed K1.2 classifier, despite the latter being written
using the verifier-final total hash view. -/
theorem exact_k12_prefix_targets_from_completed_root
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (tail : List Digest256) :
    let prefixes := input.package.root.full.projection.rootPrefixes
    k12PrefixTargetsFromAnswers configuration.machine sample.1
        (prefixes.adversary.freshQueries.map Prod.snd ++ tail) =
      prefixResolutionTargetSet (exactK12Truncate input)
        (exactK12ProverPrefixQueries input) (exactK12Roots input)
        (exactK12Openings input) := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have runtimeProjectionExact :
      exactK12Runtime input =
        operationalRootRuntime
          (configuration.machine.tapeIdentity sample.1)
          prefixes.adversaryValue prefixes.adversary.finalState
          prefixes.verifier.finalState prefixes.verifierFinalStateValue := by
    simpa [exactK12Runtime, prefixes] using prefixes.runtimeExact
  have truncateExact :
      exactK12Truncate input =
        truncateAtOracleState prefixes.verifier.finalState := by
    funext rawInput
    unfold exactK12Truncate truncateAtOracleState
    rw [runtimeProjectionExact]
    rfl
  calc
    k12PrefixTargetsFromAnswers configuration.machine sample.1
        (prefixes.adversary.freshQueries.map Prod.snd ++ tail) =
      prefixResolutionTargetSet
        (truncateAtOracleState prefixes.adversary.finalState)
        (prefixes.adversary.finalState.history.map
          (fun record : QueryRecord =>
            runtimeInputToRawHashInput record.input))
        (rootsOfReturnedValue prefixes.adversaryValue)
        (openingsOfReturnedValue prefixes.adversaryValue) :=
      k12_prefix_targets_stable_after_completed_prover
        configuration.machine sample.1 _
        input.package.root.fixedRoot.base.runtime prefixes tail
    _ = prefixResolutionTargetSet
        (truncateAtOracleState prefixes.verifier.finalState)
        (prefixes.adversary.finalState.history.map
          (fun record : QueryRecord =>
            runtimeInputToRawHashInput record.input))
        (rootsOfReturnedValue prefixes.adversaryValue)
        (openingsOfReturnedValue prefixes.adversaryValue) :=
      prefixResolutionTargetSet_eq_of_agree_on_log _ _ _
        (completed_root_truncate_views_agree_on_prover_history
          configuration.machine sample.1 _
          input.package.root.fixedRoot.base.runtime prefixes)
        _ _
    _ = prefixResolutionTargetSet (exactK12Truncate input)
        (exactK12ProverPrefixQueries input) (exactK12Roots input)
        (exactK12Openings input) := by
      rw [truncateExact]
      simp [exactK12ProverPrefixQueries, exactK12Roots,
        exactK12Openings, rootsOfReturnedValue,
        openingsOfReturnedValue, runtimeProjectionExact,
        operationalRootRuntime]

/-- Every concrete late K1.2 target hit is carried by one literal fresh
verifier coordinate.  Cached repetitions are traced back to the first new
table entry, while an entry already present at prover return would contradict
the definition of a late input. -/
theorem exact_k12_late_target_hit_has_verifier_fresh_coordinate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (lateHit : PrefixResolutionLateTargetHit (exactK12Truncate input)
      (exactK12ProverPrefixQueries input) (exactK12OrderedQueries input)
      (exactK12Roots input) (exactK12Openings input)) :
    let prefixes := input.package.root.full.projection.rootPrefixes
    ∃ target queryInput answer prior later,
      target ∈ prefixResolutionTargetSet (exactK12Truncate input)
        (exactK12ProverPrefixQueries input) (exactK12Roots input)
        (exactK12Openings input) ∧
      prefixes.verifier.freshQueries =
        prior ++ (queryInput, answer) :: later ∧
      runtimeDigest256PrefixToMerkleDigest answer = target := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  rcases lateHit with
    ⟨target, targetMember, rawInput, rawMember, rawNotPrefix, digestExact⟩
  have runtimeExact :
      exactK12Runtime input =
        operationalRootRuntime
          (configuration.machine.tapeIdentity sample.1)
          prefixes.adversaryValue prefixes.adversary.finalState
          prefixes.verifier.finalState prefixes.verifierFinalStateValue := by
    simpa [exactK12Runtime, prefixes] using prefixes.runtimeExact
  have rawMember' : rawInput ∈ prefixes.verifier.finalState.history.map
      (fun record : QueryRecord =>
        runtimeInputToRawHashInput record.input) := by
    simpa [exactK12OrderedQueries, runtimeExact, operationalRootRuntime] using
      rawMember
  have rawNotPrefix' : rawInput ∉ prefixes.adversary.finalState.history.map
      (fun record : QueryRecord =>
        runtimeInputToRawHashInput record.input) := by
    simpa [exactK12ProverPrefixQueries, runtimeExact,
      operationalRootRuntime] using rawNotPrefix
  obtain ⟨record, recordMember, rfl⟩ := List.mem_map.mp rawMember'
  have suffix := projected_fresh_returned_trace_preserves_suffix
    configuration.machine.verifierLimits .verifier
    prefixes.adversary.finalState.history []
    configuration.machine.verifierFuel prefixes.adversary.finalState
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (totalizeOracleMachine configuration.machine.verifierFuel
        (initialRawFutureFreeProgram configuration.machine.environment
          prefixes.adversaryValue.rawMessages
          configuration.machine.driverFuel)))
    prefixes.verifier.freshQueries prefixes.verifier.result
    prefixes.verifier.finalState prefixes.verifier.steps
    (projected_fresh_suffix_initial prefixes.adversary.finalState)
    prefixes.verifier.trace
  rcases suffix with ⟨appended, historyExact, _answersExact⟩
  have recordInAppended : record ∈ appended := by
    rw [historyExact] at recordMember
    rcases List.mem_append.mp recordMember with inherited | appendedMember
    · exact False.elim (rawNotPrefix'
        (List.mem_map.mpr ⟨record, inherited, rfl⟩))
    · exact appendedMember
  have recordInSegment : record ∈ historySince
      prefixes.adversary.finalState prefixes.verifier.finalState := by
    unfold historySince
    rw [historyExact]
    simpa using recordInAppended
  have retained := projected_machine_prefix_lookup_retains_segment_answer
    configuration.machine.verifierLimits .verifier
    configuration.machine.verifierFuel prefixes.adversary.finalState
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (totalizeOracleMachine configuration.machine.verifierFuel
        (initialRawFutureFreeProgram configuration.machine.environment
          prefixes.adversaryValue.rawMessages
          configuration.machine.driverFuel)))
    prefixes.adversary.remaining prefixes.verifier record recordInSegment
  cases finalLookup : lookupEntry prefixes.verifier.finalState record.input with
  | none => simp [finalLookup] at retained
  | some entry =>
      have entryOutput : entry.output = record.output := by
        simpa [finalLookup] using retained
      have beforeMissing :
          lookupEntry prefixes.adversary.finalState record.input = none := by
        cases beforeLookup :
            lookupEntry prefixes.adversary.finalState record.input with
        | none => rfl
        | some oldEntry =>
            have oldInput : oldEntry.input = record.input := by
              unfold lookupEntry at beforeLookup
              exact of_decide_eq_true
                (List.find?_eq_some_iff_append.mp beforeLookup).1
            have oldMember : oldEntry ∈ prefixes.adversary.finalState.table := by
              unfold lookupEntry at beforeLookup
              exact List.mem_of_find?_eq_some beforeLookup
            let proverController := controllerFromProjectedFreshAnswers
              emptyOracle.history
              (prefixes.adversary.freshQueries.map Prod.snd)
            have proverRun := projected_machine_prefix_returned_run_exact
              configuration.machine.adversaryLimits .adversary
              configuration.machine.adversaryFuel emptyOracle
              (schedulerStageProgram
                (SchedulerNativePlainRomResult TapeIdentity Statement
                  Tag73K12ParsedProof Payload Result)
                (totalizeOracleMachine configuration.machine.adversaryFuel
                  (configuration.machine.blackBox.start sample.1
                    configuration.machine.observation)))
              (freshAnswerTapeToList sample.2) prefixes.adversary
              empty_oracle_history_total_coherent
            have oldNewMember : oldEntry ∈
                (runMachine proverController
                  configuration.machine.adversaryLimits .adversary
                  configuration.machine.adversaryFuel emptyOracle
                  (schedulerStageProgram
                    (SchedulerNativePlainRomResult TapeIdentity Statement
                      Tag73K12ParsedProof Payload Result)
                    (totalizeOracleMachine configuration.machine.adversaryFuel
                      (configuration.machine.blackBox.start sample.1
                        configuration.machine.observation)))).oracle.table.drop
                    emptyOracle.table.length := by
              change oldEntry ∈
                (runMachine
                  (controllerFromProjectedFreshAnswers emptyOracle.history
                    (prefixes.adversary.freshQueries.map Prod.snd))
                  configuration.machine.adversaryLimits .adversary
                  configuration.machine.adversaryFuel emptyOracle
                  (schedulerStageProgram
                    (SchedulerNativePlainRomResult TapeIdentity Statement
                      Tag73K12ParsedProof Payload Result)
                    (totalizeOracleMachine configuration.machine.adversaryFuel
                      (configuration.machine.blackBox.start sample.1
                        configuration.machine.observation)))).oracle.table.drop
                    emptyOracle.table.length
              rw [proverRun]
              simpa [emptyOracle] using oldMember
            have oldFresh := run_machine_new_entry_is_fresh_and_initially_absent
              proverController configuration.machine.adversaryLimits
              .adversary configuration.machine.adversaryFuel emptyOracle
              (schedulerStageProgram
                (SchedulerNativePlainRomResult TapeIdentity Statement
                  Tag73K12ParsedProof Payload Result)
                (totalizeOracleMachine configuration.machine.adversaryFuel
                  (configuration.machine.blackBox.start sample.1
                    configuration.machine.observation)))
              oldEntry oldNewMember
            rw [proverRun] at oldFresh
            rcases oldFresh.2.2 with
              ⟨oldRecord, oldRecordMember, _oldActor, _oldOrigin,
                oldRecordInput, _oldRecordOutput, _oldExact⟩
            exact False.elim (rawNotPrefix'
              (List.mem_map.mpr ⟨oldRecord, by
                simpa [historySince, emptyOracle] using oldRecordMember,
                by rw [oldRecordInput, oldInput]⟩))
      obtain ⟨tableSuffix, tableExtension⟩ :=
        projected_machine_prefix_table_extension
          configuration.machine.verifierLimits .verifier
          configuration.machine.verifierFuel prefixes.adversary.finalState
          (schedulerStageProgram
            (SchedulerNativePlainRomResult TapeIdentity Statement
              Tag73K12ParsedProof Payload Result)
            (totalizeOracleMachine configuration.machine.verifierFuel
              (initialRawFutureFreeProgram configuration.machine.environment
                prefixes.adversaryValue.rawMessages
                configuration.machine.driverFuel)))
          prefixes.adversary.remaining prefixes.verifier
      have entryNew := lookupEntry_new_suffix_member
        prefixes.adversary.finalState prefixes.verifier.finalState tableSuffix
        tableExtension record.input entry beforeMissing finalLookup
      let verifierController := controllerFromProjectedFreshAnswers
        prefixes.adversary.finalState.history
        (prefixes.verifier.freshQueries.map Prod.snd)
      have verifierRun := projected_machine_prefix_returned_run_exact
        configuration.machine.verifierLimits .verifier
        configuration.machine.verifierFuel prefixes.adversary.finalState
        (schedulerStageProgram
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)
          (totalizeOracleMachine configuration.machine.verifierFuel
            (initialRawFutureFreeProgram configuration.machine.environment
              prefixes.adversaryValue.rawMessages
              configuration.machine.driverFuel)))
        prefixes.adversary.remaining prefixes.verifier
        prefixes.adversary.finalCoherent
      have entryFresh := run_machine_new_entry_is_fresh_and_initially_absent
        verifierController configuration.machine.verifierLimits .verifier
        configuration.machine.verifierFuel prefixes.adversary.finalState
        (schedulerStageProgram
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)
          (totalizeOracleMachine configuration.machine.verifierFuel
            (initialRawFutureFreeProgram configuration.machine.environment
              prefixes.adversaryValue.rawMessages
              configuration.machine.driverFuel)))
        entry (by simpa [verifierController, verifierRun] using entryNew)
      rw [verifierRun] at entryFresh
      rcases entryFresh.2.2 with
        ⟨freshRecord, freshRecordMember, _freshActor, freshOrigin,
          _freshInput, freshOutput, _freshExact⟩
      have answerMember : freshRecord.output ∈
          prefixes.verifier.freshQueries.map Prod.snd := by
        have enumerated := fresh_record_output_mem_fresh_answer_enumeration
          (historySince prefixes.adversary.finalState
            prefixes.verifier.finalState)
          freshRecord freshRecordMember freshOrigin
        rw [projected_machine_prefix_fresh_answers_are_history_suffix
          configuration.machine.verifierLimits .verifier
          configuration.machine.verifierFuel prefixes.adversary.finalState
          (schedulerStageProgram
            (SchedulerNativePlainRomResult TapeIdentity Statement
              Tag73K12ParsedProof Payload Result)
            (totalizeOracleMachine configuration.machine.verifierFuel
              (initialRawFutureFreeProgram configuration.machine.environment
                prefixes.adversaryValue.rawMessages
                configuration.machine.driverFuel)))
          prefixes.adversary.remaining prefixes.verifier] at enumerated
        exact enumerated
      obtain ⟨queryPair, queryPairMember, queryAnswerExact⟩ :=
        List.mem_map.mp answerMember
      rcases queryPair with ⟨queryInput, answer⟩
      obtain ⟨prior, later, decomposition⟩ :=
        (List.mem_iff_append).mp queryPairMember
      have truncateExact : runtimeDigest256PrefixToMerkleDigest entry.output =
          target := by
        have digestExact' := digestExact
        unfold exactK12Truncate at digestExact'
        rw [runtimeExact] at digestExact'
        simpa [operationalRootRuntime,
          rawHashInputToRuntimeInput_roundtrip, finalLookup] using digestExact'
      refine ⟨target, queryInput, answer, prior, later, targetMember,
        decomposition, ?_⟩
      have answerExact : answer = freshRecord.output := by
        simpa using queryAnswerExact
      rw [answerExact, freshOutput]
      exact truncateExact

def schedulerNativeRequestActor?
    {globalOracleCalls : Nat} {Result : Type} :
    SchedulerNativeRequest globalOracleCalls Result → Option QueryActor
  | .machineFresh _limits _limitBound actor _state _input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
      some actor
  | .returned _ | .failed _ | .transitionLimit | .forkOutput .. |
      .forkAdvance .. => none

theorem scheduler_native_request_actor_of_exact_machine_fresh
    {globalOracleCalls : Nat} {Result : Type}
    {actor : QueryActor} {state : OracleState} {input : ShaInput}
    {request : SchedulerNativeRequest globalOracleCalls Result}
    (exact : IsExactSchedulerNativeMachineFreshRequest actor state input
      request) :
    schedulerNativeRequestActor? request = some actor := by
  cases exact
  rfl

/-! ## Executable prefix accounting for the budgeted tree -/

/-- Number of literal root-verifier fresh coordinates in one answer prefix.
The count follows the result-carrying scheduler, so adversary, fork, and
padding coordinates contribute zero. -/
def schedulerVerifierRequestCount
    {globalOracleCalls : Nat} {Final : Type} (transitionFuel : Nat) :
    SchedulerNativeCursor globalOracleCalls Final → List Digest256 → Nat
  | _cursor, [] => 0
  | cursor, answer :: rest =>
      let request := seekSchedulerNativeExposure transitionFuel cursor
      (if schedulerNativeRequestActor? request = some .verifier then 1 else 0) +
        schedulerVerifierRequestCount transitionFuel
          (schedulerNativeRequestNext request answer) rest

@[simp] theorem scheduler_verifier_request_count_append
    {globalOracleCalls : Nat} {Final : Type}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Final)
    (first second : List Digest256) :
    schedulerVerifierRequestCount transitionFuel cursor (first ++ second) =
      schedulerVerifierRequestCount transitionFuel cursor first +
        schedulerVerifierRequestCount transitionFuel
          (schedulerNativePrefixCursor transitionFuel cursor first) second := by
  induction first generalizing cursor with
  | nil => simp [schedulerVerifierRequestCount, schedulerNativePrefixCursor]
  | cons answer rest ih =>
      simp only [List.cons_append, schedulerVerifierRequestCount,
        schedulerNativePrefixCursor]
      rw [ih]
      omega

/-- Prefix counting depends only on the exposed request, not on proof fields
inside two extensionally aligned native cursors. -/
theorem scheduler_verifier_request_count_congr
    {globalOracleCalls : Nat} {Final : Type}
    (transitionFuel : Nat)
    (left right : SchedulerNativeCursor globalOracleCalls Final)
    (answers : List Digest256)
    (aligned : seekSchedulerNativeExposure transitionFuel left =
      seekSchedulerNativeExposure transitionFuel right) :
    schedulerVerifierRequestCount transitionFuel left answers =
      schedulerVerifierRequestCount transitionFuel right answers := by
  induction answers generalizing left right with
  | nil => rfl
  | cons answer rest ih =>
      simp only [schedulerVerifierRequestCount]
      rw [aligned]

/-- Every consumed prefix of one proof-relevant machine segment has the
literal actor count.  In particular, adversary coordinates consume no K1.2
budget and verifier coordinates consume exactly one unit each. -/
theorem projected_fresh_trace_scheduler_verifier_count_prefix
    {globalOracleCalls : Nat} {Final MachineResult : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final) :
    ∀ {fuel : Nat} {entryState : OracleState}
      {program : OracleMachine MachineResult}
      {freshQueries : List (ShaInput × Digest256)}
      {result : MachineResult} {finalState : OracleState} {steps : Nat}
      (coherent : HistoryTotalCoherent entryState)
      (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
        freshQueries result finalState steps)
      (prior later : List (ShaInput × Digest256)),
      freshQueries = prior ++ later →
        schedulerVerifierRequestCount transitionFuel
            (.machine limits limitBound actor entryState program fuel coherent
              onReturned)
            (prior.map Prod.snd) =
          if actor = .verifier then prior.length else 0 := by
  intro fuel entryState program freshQueries result finalState steps coherent
    trace
  induction trace with
  | returned fuel state program traceCoherent result finalState steps sought =>
      intro prior later decomposition
      have empty : prior = [] := by
        apply List.length_eq_zero_iff.mp
        have lengths := congrArg List.length decomposition
        simp only [List.length_nil, List.length_append] at lengths
        omega
      subst prior
      simp [schedulerVerifierRequestCount]
  | fresh fuel state requestState program traceCoherent headInput nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought headAnswer rest result finalState tailSteps tail ih =>
      intro prior later decomposition
      cases prior with
      | nil => simp [schedulerVerifierRequestCount]
      | cons priorHead priorTail =>
          rcases priorHead with ⟨priorInput, priorAnswer⟩
          simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq] at decomposition
          rcases decomposition with
            ⟨⟨inputExact, answerExact⟩, tailExact⟩
          subst priorInput
          subst priorAnswer
          cases transitionFuel with
          | zero => omega
          | succ current =>
              simp only [List.map_cons, schedulerVerifierRequestCount]
              rw [seek_scheduler_native_exposure_machine_of_fresh current
                limits limitBound actor fuel state requestState program
                traceCoherent headInput nextProgram remainingFuel cachedSteps
                requestCoherent totalRoom freshRoom missing onReturned sought]
              simp only [schedulerNativeRequestActor?,
                schedulerNativeRequestNext]
              rw [ih
                (fresh_query_state_preserves_history_total_coherent actor
                  requestState headInput headAnswer requestCoherent)
                priorTail later tailExact]
              by_cases verifier : actor = .verifier
              · subst actor
                simp
                omega
              · simp [verifier]

/-- List presentation of a budgeted-tree hit.  It is convenient for exact
prefix decompositions; the indexed finite-tape theorem below reconnects it to
the probability experiment without changing the event. -/
def budgetedEverHitsList
    {Output : Type} [DecidableEq Output] {targetCap : Nat} :
    {caps : List Nat} → {budget : Nat} →
      BudgetedCausalTargetTree Output targetCap caps budget →
        List Output → Prop
  | [], _, .done _, _ => False
  | _ :: _, _, .free next, [] => False
  | _ :: _, _, .free next, output :: rest =>
      budgetedEverHitsList (next output) rest
  | _ :: _, _, .charged targets _ next, [] => False
  | _ :: _, _, .charged targets _ next, output :: rest =>
      output ∈ targets ∨ budgetedEverHitsList (next output) rest

theorem budgeted_ever_hits_iff_ever_hits_list
    {Output : Type} [DecidableEq Output] {targetCap budget : Nat}
    {caps : List Nat}
    (tree : BudgetedCausalTargetTree Output targetCap caps budget)
    (tape : FreshAnswerTape Output caps.length) :
    tree.toCausal.everHits tape ↔
      budgetedEverHitsList tree (freshAnswerTapeToList tape) := by
  induction tree with
  | done => rfl
  | free next ih =>
      rcases tape with ⟨output, tail⟩
      simpa [BudgetedCausalTargetTree.toCausal,
        CausalTargetTree.everHits, budgetedEverHitsList,
        freshAnswerTapeToList] using ih output tail
  | charged targets targetCardLe next ih =>
      rcases tape with ⟨output, tail⟩
      simpa [BudgetedCausalTargetTree.toCausal,
        CausalTargetTree.everHits, budgetedEverHitsList,
        freshAnswerTapeToList] using or_congr_right (ih output tail)

/-- Follow the root cursor for a fixed number of padded master coordinates.
The budget index is consumed only by literal root-verifier fresh requests.
If a malformed execution somehow reaches another verifier request after the
supplied budget is exhausted, that coordinate is left free; the operational
fuel lemma rules this branch out for completed exact inputs. -/
def k12BudgetedSchedulerTreeFrom
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    {globalOracleCalls : Nat} {Final : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (transitionFuel : Nat) :
    (remaining budget : Nat) → List Digest256 →
      SchedulerNativeCursor globalOracleCalls Final →
      BudgetedCausalTargetTree Digest256 K12RuntimeTargetCap
        (k12RuntimeCaps remaining) budget
  | 0, budget, _answers, _cursor => .done budget
  | remaining + 1, budget, answers, cursor =>
      let request := seekSchedulerNativeExposure transitionFuel cursor
      if verifierRequest : schedulerNativeRequestActor? request =
          some .verifier then
        match budget with
        | 0 =>
            .free fun answer =>
              k12BudgetedSchedulerTreeFrom machine hidden transitionFuel
                remaining 0 (answers ++ [answer])
                (schedulerNativeRequestNext request answer)
        | tailBudget + 1 =>
            let targets := k12PrefixTargetsFromAnswers machine hidden answers
            .charged (deployedPrefixTargetPreimage targets)
              (k12_runtime_targets_from_answers_card_le machine hidden answers)
              fun answer =>
                k12BudgetedSchedulerTreeFrom machine hidden transitionFuel
                  remaining tailBudget (answers ++ [answer])
                  (schedulerNativeRequestNext request answer)
      else
        .free fun answer =>
          k12BudgetedSchedulerTreeFrom machine hidden transitionFuel remaining
            budget (answers ++ [answer])
            (schedulerNativeRequestNext request answer)

/-- Direct list semantics of the scheduler target experiment.  This separates
ordinary prefix induction from the dependent cap index of the counted tree. -/
def k12SchedulerHitsListFrom
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    {globalOracleCalls : Nat} {Final : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (transitionFuel : Nat)
    (budget : Nat) (answers : List Digest256) :
    (cursor : SchedulerNativeCursor globalOracleCalls Final) →
      List Digest256 → Prop
  | _cursor, [] => False
  | cursor, answer :: rest =>
      let request := seekSchedulerNativeExposure transitionFuel cursor
      if schedulerNativeRequestActor? request = some .verifier then
        match budget with
        | 0 => k12SchedulerHitsListFrom machine hidden transitionFuel 0
            (answers ++ [answer])
            (schedulerNativeRequestNext request answer) rest
        | tailBudget + 1 =>
            answer ∈ deployedPrefixTargetPreimage
                (k12PrefixTargetsFromAnswers machine hidden answers) ∨
              k12SchedulerHitsListFrom machine hidden transitionFuel tailBudget
                (answers ++ [answer])
                (schedulerNativeRequestNext request answer) rest
      else
        k12SchedulerHitsListFrom machine hidden transitionFuel budget
          (answers ++ [answer])
          (schedulerNativeRequestNext request answer) rest

/-- The direct list semantics is exactly the erasure of the counted dependent
tree whenever the supplied list has the tree's declared remaining length. -/
theorem k12_budgeted_tree_ever_hits_list_iff
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    {globalOracleCalls : Nat} {Final : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (transitionFuel : Nat) :
    ∀ (remaining budget : Nat) (answers : List Digest256)
      (cursor : SchedulerNativeCursor globalOracleCalls Final)
      (tape : List Digest256),
      tape.length = remaining →
        (budgetedEverHitsList
            (k12BudgetedSchedulerTreeFrom machine hidden transitionFuel
              remaining budget answers cursor) tape ↔
          k12SchedulerHitsListFrom machine hidden transitionFuel budget answers
            cursor tape) := by
  intro remaining budget answers cursor tape
  intro lengthExact
  induction remaining generalizing budget answers cursor tape with
  | zero =>
      have empty : tape = [] := List.length_eq_zero_iff.mp lengthExact
      subst tape
      rfl
  | succ remaining inductionHypothesis =>
      cases tape with
      | nil => simp at lengthExact
      | cons answer rest =>
          have restLength : rest.length = remaining := by
            simpa using lengthExact
          change budgetedEverHitsList
              (k12BudgetedSchedulerTreeFrom machine hidden transitionFuel
                (Nat.succ remaining) budget answers cursor)
              (answer :: rest) ↔
            k12SchedulerHitsListFrom machine hidden transitionFuel budget
              answers cursor (answer :: rest)
          unfold k12BudgetedSchedulerTreeFrom k12SchedulerHitsListFrom
          by_cases verifierRequest :
              schedulerNativeRequestActor?
                  (seekSchedulerNativeExposure transitionFuel cursor) =
                some .verifier
          · rw [dif_pos verifierRequest, if_pos verifierRequest]
            cases budget with
            | zero =>
                change budgetedEverHitsList
                    (k12BudgetedSchedulerTreeFrom machine hidden transitionFuel
                      remaining 0 (answers ++ [answer])
                      (schedulerNativeRequestNext
                        (seekSchedulerNativeExposure transitionFuel cursor)
                        answer)) rest ↔
                  k12SchedulerHitsListFrom machine hidden transitionFuel 0
                    (answers ++ [answer])
                    (schedulerNativeRequestNext
                      (seekSchedulerNativeExposure transitionFuel cursor)
                      answer) rest
                exact inductionHypothesis 0 (answers ++ [answer])
                  (schedulerNativeRequestNext
                    (seekSchedulerNativeExposure transitionFuel cursor)
                    answer) rest restLength
            | succ tailBudget =>
                change answer ∈ deployedPrefixTargetPreimage
                      (k12PrefixTargetsFromAnswers machine hidden answers) ∨
                    budgetedEverHitsList
                      (k12BudgetedSchedulerTreeFrom machine hidden
                        transitionFuel remaining tailBudget
                        (answers ++ [answer])
                        (schedulerNativeRequestNext
                          (seekSchedulerNativeExposure transitionFuel cursor)
                          answer)) rest ↔
                  answer ∈ deployedPrefixTargetPreimage
                      (k12PrefixTargetsFromAnswers machine hidden answers) ∨
                    k12SchedulerHitsListFrom machine hidden transitionFuel
                      tailBudget (answers ++ [answer])
                      (schedulerNativeRequestNext
                        (seekSchedulerNativeExposure transitionFuel cursor)
                        answer) rest
                exact or_congr_right
                  (inductionHypothesis tailBudget (answers ++ [answer])
                    (schedulerNativeRequestNext
                      (seekSchedulerNativeExposure transitionFuel cursor)
                      answer) rest restLength)
          · rw [dif_neg verifierRequest, if_neg verifierRequest]
            change budgetedEverHitsList
                (k12BudgetedSchedulerTreeFrom machine hidden transitionFuel
                  remaining budget (answers ++ [answer])
                  (schedulerNativeRequestNext
                    (seekSchedulerNativeExposure transitionFuel cursor)
                    answer)) rest ↔
              k12SchedulerHitsListFrom machine hidden transitionFuel budget
                (answers ++ [answer])
                (schedulerNativeRequestNext
                  (seekSchedulerNativeExposure transitionFuel cursor) answer)
                rest
            exact inductionHypothesis budget (answers ++ [answer])
                (schedulerNativeRequestNext
                  (seekSchedulerNativeExposure transitionFuel cursor) answer)
                rest restLength

/-- If a concrete answer prefix reaches a verifier-fresh coordinate before
the verifier budget is exhausted and that coordinate hits the causal K1.2
target set, the direct scheduler experiment records a hit. -/
theorem k12_scheduler_hits_list_at_verifier_prefix
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    {globalOracleCalls : Nat} {Final : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Final)
    (answers : List Digest256) (budget : Nat)
    (priorAnswers : List Digest256) (answer : Digest256)
    (suffix : List Digest256)
    (budgetRoom :
      schedulerVerifierRequestCount transitionFuel cursor priorAnswers < budget)
    (requestVerifier :
      schedulerNativeRequestActor?
          (seekSchedulerNativeExposure transitionFuel
            (schedulerNativePrefixCursor transitionFuel cursor priorAnswers)) =
        some .verifier)
    (targetHit : answer ∈ deployedPrefixTargetPreimage
      (k12PrefixTargetsFromAnswers machine hidden (answers ++ priorAnswers))) :
    k12SchedulerHitsListFrom machine hidden transitionFuel budget answers cursor
      (priorAnswers ++ answer :: suffix) := by
  induction priorAnswers generalizing cursor answers budget with
  | nil =>
      simp only [schedulerVerifierRequestCount] at budgetRoom
      obtain ⟨tailBudget, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt budgetRoom)
      simp only [List.nil_append]
      unfold k12SchedulerHitsListFrom
      rw [if_pos (by simpa [schedulerNativePrefixCursor] using requestVerifier)]
      exact Or.inl (by simpa using targetHit)
  | cons head tail inductionHypothesis =>
      let request := seekSchedulerNativeExposure transitionFuel cursor
      let nextCursor := schedulerNativeRequestNext request head
      have nextRequestVerifier :
          schedulerNativeRequestActor?
              (seekSchedulerNativeExposure transitionFuel
                (schedulerNativePrefixCursor transitionFuel nextCursor tail)) =
            some .verifier := by
        simpa [nextCursor, request, schedulerNativePrefixCursor] using
          requestVerifier
      have nextTargetHit : answer ∈ deployedPrefixTargetPreimage
          (k12PrefixTargetsFromAnswers machine hidden
            ((answers ++ [head]) ++ tail)) := by
        simpa [List.append_assoc] using targetHit
      by_cases currentVerifier :
          schedulerNativeRequestActor? request = some .verifier
      · obtain ⟨tailBudget, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) budgetRoom))
        have tailRoom :
            schedulerVerifierRequestCount transitionFuel nextCursor tail <
              tailBudget := by
          have counted : 1 +
                schedulerVerifierRequestCount transitionFuel nextCursor tail ≤
              tailBudget := by
            simpa [schedulerVerifierRequestCount, request, nextCursor,
              currentVerifier] using budgetRoom
          omega
        have tailHit := inductionHypothesis nextCursor (answers ++ [head])
          tailBudget tailRoom nextRequestVerifier nextTargetHit
        simp only [List.cons_append]
        unfold k12SchedulerHitsListFrom
        rw [if_pos (by simpa [request] using currentVerifier)]
        exact Or.inr tailHit
      · have tailRoom :
            schedulerVerifierRequestCount transitionFuel nextCursor tail <
              budget := by
          simpa [schedulerVerifierRequestCount, request, nextCursor,
            currentVerifier] using budgetRoom
        have tailHit := inductionHypothesis nextCursor (answers ++ [head])
          budget tailRoom nextRequestVerifier nextTargetHit
        simp only [List.cons_append]
        unfold k12SchedulerHitsListFrom
        rw [if_neg (by simpa [request] using currentVerifier)]
        exact tailHit

/-! ## Exact completed-root alignment -/

/-- Consuming equal answer prefixes preserves equality of the next exposed
native request. -/
theorem seek_native_prefix_congr_for_k12
    {globalOracleCalls : Nat} {Final : Type}
    (transitionFuel : Nat)
    (left right : SchedulerNativeCursor globalOracleCalls Final)
    (answers : List Digest256)
    (aligned : seekSchedulerNativeExposure transitionFuel left =
      seekSchedulerNativeExposure transitionFuel right) :
    seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel left answers) =
      seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel right answers) := by
  induction answers generalizing left right with
  | nil => exact aligned
  | cons answer rest inductionHypothesis =>
      simp only [schedulerNativePrefixCursor]
      rw [aligned]

/-- A returned projected trace reaches its literal callback with the one
normalization transition consumed by the machine return. -/
theorem projected_fresh_trace_reaches_returned_native_predecessor_for_k12
    {globalOracleCalls : Nat} {Final MachineResult : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final) :
    ∀ {fuel : Nat} {entryState : OracleState}
      {program : OracleMachine MachineResult}
      {freshQueries : List (ShaInput × Digest256)}
      {result : MachineResult} {finalState : OracleState} {steps : Nat}
      (coherent : HistoryTotalCoherent entryState)
      (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
        freshQueries result finalState steps)
      (finalCoherent : HistoryTotalCoherent finalState),
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (.machine limits limitBound actor entryState program fuel coherent
              onReturned)
            (freshQueries.map Prod.snd)) =
        seekSchedulerNativeExposure (transitionFuel - 1)
          (onReturned result finalState finalCoherent) := by
  intro fuel entryState program freshQueries result finalState steps coherent
    trace
  induction trace with
  | returned fuel state program traceCoherent result finalState steps sought =>
      intro finalCoherent
      have coherentExact : coherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      cases transitionFuel with
      | zero => omega
      | succ current =>
          simp only [List.map_nil, schedulerNativePrefixCursor]
          rw [seek_scheduler_native_exposure_machine_of_returned current limits
            limitBound actor fuel state program traceCoherent onReturned result
              finalState steps sought]
          simp only [Nat.add_sub_cancel]
  | fresh fuel state requestState program traceCoherent input next
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought answer rest result finalState tailSteps tail
      inductionHypothesis =>
      intro finalCoherent
      have coherentExact : coherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      cases transitionFuel with
      | zero => omega
      | succ current =>
          simp only [List.map_cons, schedulerNativePrefixCursor]
          rw [seek_scheduler_native_exposure_machine_of_fresh current limits
            limitBound actor fuel state requestState program traceCoherent input
              next remainingFuel cachedSteps requestCoherent totalRoom freshRoom
                missing onReturned sought]
          exact inductionHypothesis
            (fresh_query_state_preserves_history_total_coherent actor
              requestState input answer requestCoherent)
            finalCoherent

/-- Structure-level wrapper around the predecessor-fuel traversal. -/
theorem projected_machine_prefix_reaches_returned_native_predecessor_for_k12
    {globalOracleCalls : Nat} {Final MachineResult : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (coherent : HistoryTotalCoherent entryState)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel entryState
      program available) :
    seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel
          (.machine limits limitBound actor entryState program fuel coherent
            onReturned)
          (returned.freshQueries.map Prod.snd)) =
      seekSchedulerNativeExposure (transitionFuel - 1)
        (onReturned returned.result returned.finalState
          returned.finalCoherent) := by
  exact projected_fresh_trace_reaches_returned_native_predecessor_for_k12
    transitionFuel positive limits limitBound actor onReturned coherent
      returned.trace returned.finalCoherent

/-- If a returned projected segment contains a fresh coordinate, increasing
the normalization allowance by one does not change its first exposed fresh
request. -/
theorem projected_nonempty_fresh_prefix_seek_predecessor_eq_for_k12
    {globalOracleCalls : Nat} {Final MachineResult : Type}
    (transitionFuel : Nat) (transitionRoom : 2 ≤ transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (coherent : HistoryTotalCoherent entryState)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final)
    {freshQueries : List (ShaInput × Digest256)}
    {result : MachineResult} {finalState : OracleState} {steps : Nat}
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps)
    (nonempty : freshQueries ≠ []) :
    seekSchedulerNativeExposure (transitionFuel - 1)
        (.machine limits limitBound actor entryState program fuel coherent
          onReturned) =
      seekSchedulerNativeExposure transitionFuel
        (.machine limits limitBound actor entryState program fuel coherent
          onReturned) := by
  cases trace with
  | returned fuel state program traceCoherent result finalState steps sought =>
      exact (nonempty rfl).elim
  | fresh fuel state requestState program traceCoherent input next
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought answer rest result finalState tailSteps tail =>
      have coherentExact : coherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      let previous := transitionFuel - 2
      have predecessorExact : transitionFuel - 1 = previous + 1 := by
        dsimp only [previous]
        omega
      have fullExact : transitionFuel = (previous + 1) + 1 := by
        dsimp only [previous]
        omega
      rw [predecessorExact]
      rw [seek_scheduler_native_exposure_machine_of_fresh previous limits
        limitBound actor fuel entryState requestState program coherent input
        next remainingFuel cachedSteps requestCoherent totalRoom freshRoom
        missing onReturned sought]
      rw [fullExact]
      rw [seek_scheduler_native_exposure_machine_of_fresh (previous + 1)
        limits limitBound actor fuel entryState requestState program coherent
        input next remainingFuel cachedSteps requestCoherent totalRoom freshRoom
        missing onReturned sought]

/-- A positional coordinate of the completed verifier prefix is a charged
verifier request of the exact full scheduler, and fewer than the available
verifier-fuel units precede it. -/
theorem exact_k12_verifier_coordinate_has_budget_and_request
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (queryInput : ShaInput) (answer : Digest256)
    (prior later : List (ShaInput × Digest256))
    (decomposition :
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        prior ++ (queryInput, answer) :: later) :
    let prefixes := input.package.root.full.projection.rootPrefixes
    let globalPrior := prefixes.adversary.freshQueries.map Prod.snd ++
      prior.map Prod.snd
    schedulerVerifierRequestCount transitionFuel
          (exactPlainRomCursor configuration sample.1) globalPrior <
        configuration.machine.verifierFuel ∧
      schedulerNativeRequestActor?
          (seekSchedulerNativeExposure transitionFuel
            (schedulerNativePrefixCursor transitionFuel
              (exactPlainRomCursor configuration sample.1) globalPrior)) =
      some .verifier := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  dsimp only
  have positive : 0 < transitionFuel := by omega
  have rootListCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (exactPlainRomRootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        .returned (.completed input.package.root.fixedRoot.base.runtime
          input.package.root.fixedRoot.base.clientRun) := by
    rw [← run_scheduler_native_terminal_eq_list]
    exact input.package.root.fixedRoot.base.rootCompleted
  let stages := completed_root_constructs_operational_stages transitionFuel
    positive configuration.machine sample.1 configuration.rootLimitBounds
    configuration.restorationConfiguration (freshAnswerTapeToList sample.2)
    input.package.root.fixedRoot.base.runtime
    input.package.root.fixedRoot.base.clientRun (by
      simpa [exactPlainRomRootCursor] using rootListCompleted)
  have adversaryExact :=
    completed_root_stages_and_full_prefix_adversary_exact
      (Result := Result) stages prefixes
  have verifierRoom : StageHasOracleRoom
      configuration.machine.verifierLimits prefixes.adversary.finalState
      configuration.machine.verifierFuel := by
    simpa only [← adversaryExact.2] using stages.verifierRoom
  have rootCursorExact := exact_plain_rom_cursor_eq_root_machine_of_room
    configuration sample.1 stages.adversaryRoom
  have adversaryCallbackExact :
      fullRootAdversaryReturnedContinuation configuration sample.1
          prefixes.adversary.result prefixes.adversary.finalState
          prefixes.adversary.finalCoherent =
        fullRootVerifierCursor configuration sample.1
          prefixes.adversaryValue prefixes.adversary.finalState
          prefixes.adversary.finalCoherent := by
    rw [prefixes.adversaryResult]
    simp only [fullRootAdversaryReturnedContinuation, if_pos verifierRoom]
  have afterAdversaryAligned :
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (exactPlainRomCursor configuration sample.1)
            (prefixes.adversary.freshQueries.map Prod.snd)) =
        seekSchedulerNativeExposure transitionFuel
          (fullRootVerifierCursor configuration sample.1
            prefixes.adversaryValue prefixes.adversary.finalState
            prefixes.adversary.finalCoherent) := by
    rw [rootCursorExact]
    calc
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (.machine configuration.machine.adversaryLimits
              configuration.rootLimitBounds.adversary .adversary emptyOracle
              (schedulerStageProgram
                (SchedulerNativePlainRomResult TapeIdentity Statement
                  Tag73K12ParsedProof Payload Result)
                (totalizeOracleMachine configuration.machine.adversaryFuel
                  (configuration.machine.blackBox.start sample.1
                    configuration.machine.observation)))
              configuration.machine.adversaryFuel
              empty_oracle_history_total_coherent
              (fullRootAdversaryReturnedContinuation configuration sample.1))
            (prefixes.adversary.freshQueries.map Prod.snd)) =
        seekSchedulerNativeExposure transitionFuel
          (fullRootAdversaryReturnedContinuation configuration sample.1
            prefixes.adversary.result prefixes.adversary.finalState
            prefixes.adversary.finalCoherent) :=
        (projected_machine_prefix_reaches_returned_native_predecessor_for_k12
          transitionFuel positive configuration.machine.adversaryLimits
          configuration.rootLimitBounds.adversary .adversary
          configuration.machine.adversaryFuel emptyOracle
          (schedulerStageProgram
            (SchedulerNativePlainRomResult TapeIdentity Statement
              Tag73K12ParsedProof Payload Result)
            (totalizeOracleMachine configuration.machine.adversaryFuel
              (configuration.machine.blackBox.start sample.1
                configuration.machine.observation)))
          empty_oracle_history_total_coherent
          (fullRootAdversaryReturnedContinuation configuration sample.1)
          (freshAnswerTapeToList sample.2) prefixes.adversary).trans
          (by
            rw [adversaryCallbackExact]
            apply projected_nonempty_fresh_prefix_seek_predecessor_eq_for_k12
              transitionFuel transitionRoom
              configuration.machine.verifierLimits
              configuration.rootLimitBounds.verifier .verifier
              configuration.machine.verifierFuel
              prefixes.adversary.finalState
              (schedulerStageProgram
                (SchedulerNativePlainRomResult TapeIdentity Statement
                  Tag73K12ParsedProof Payload Result)
                (totalizeOracleMachine configuration.machine.verifierFuel
                  (initialRawFutureFreeProgram configuration.machine.environment
                    prefixes.adversaryValue.rawMessages
                    configuration.machine.driverFuel)))
              prefixes.adversary.finalCoherent
              (fullRootVerifierReturnedContinuation configuration sample.1
                prefixes.adversaryValue prefixes.adversary.finalState)
              prefixes.verifier.trace
            rw [decomposition]
            simp)
      _ = _ := by rw [adversaryCallbackExact]
  obtain ⟨requestState, _historyPrefix, localRequest⟩ :=
    projected_machine_prefix_has_exact_native_request_at_prefix
      transitionFuel positive configuration.machine.verifierLimits
      configuration.rootLimitBounds.verifier .verifier
      configuration.machine.verifierFuel prefixes.adversary.finalState
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (totalizeOracleMachine configuration.machine.verifierFuel
          (initialRawFutureFreeProgram configuration.machine.environment
            prefixes.adversaryValue.rawMessages
            configuration.machine.driverFuel)))
      prefixes.adversary.finalCoherent
      (fullRootVerifierReturnedContinuation configuration sample.1
        prefixes.adversaryValue prefixes.adversary.finalState)
      prefixes.adversary.remaining prefixes.verifier prior queryInput answer
      later decomposition
  have localActor :
      schedulerNativeRequestActor?
          (seekSchedulerNativeExposure transitionFuel
            (schedulerNativePrefixCursor transitionFuel
              (fullRootVerifierCursor configuration sample.1
                prefixes.adversaryValue prefixes.adversary.finalState
                prefixes.adversary.finalCoherent)
              (prior.map Prod.snd))) = some .verifier := by
    exact scheduler_native_request_actor_of_exact_machine_fresh localRequest
  have globalRequestExact :=
    seek_native_prefix_congr_for_k12 transitionFuel
    (schedulerNativePrefixCursor transitionFuel
      (exactPlainRomCursor configuration sample.1)
      (prefixes.adversary.freshQueries.map Prod.snd))
    (fullRootVerifierCursor configuration sample.1
      prefixes.adversaryValue prefixes.adversary.finalState
      prefixes.adversary.finalCoherent)
    (prior.map Prod.snd) afterAdversaryAligned
  have globalActor :
      schedulerNativeRequestActor?
          (seekSchedulerNativeExposure transitionFuel
            (schedulerNativePrefixCursor transitionFuel
              (exactPlainRomCursor configuration sample.1)
              (prefixes.adversary.freshQueries.map Prod.snd ++
                prior.map Prod.snd))) = some .verifier := by
    rw [scheduler_native_prefix_cursor_append, globalRequestExact]
    exact localActor
  have adversaryCount :
      schedulerVerifierRequestCount transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (prefixes.adversary.freshQueries.map Prod.snd) = 0 := by
    rw [rootCursorExact]
    have countExact := projected_fresh_trace_scheduler_verifier_count_prefix
      transitionFuel positive configuration.machine.adversaryLimits
      configuration.rootLimitBounds.adversary .adversary
      (fullRootAdversaryReturnedContinuation configuration sample.1)
      empty_oracle_history_total_coherent prefixes.adversary.trace
      prefixes.adversary.freshQueries [] (by simp)
    simpa only [if_neg (by decide : QueryActor.adversary ≠ .verifier)] using
      countExact
  have localCount :
      schedulerVerifierRequestCount transitionFuel
          (fullRootVerifierCursor configuration sample.1
            prefixes.adversaryValue prefixes.adversary.finalState
            prefixes.adversary.finalCoherent)
          (prior.map Prod.snd) = prior.length := by
    unfold fullRootVerifierCursor
    have countExact :=
      projected_fresh_trace_scheduler_verifier_count_prefix
        transitionFuel positive configuration.machine.verifierLimits
        configuration.rootLimitBounds.verifier .verifier
        (fullRootVerifierReturnedContinuation configuration sample.1
          prefixes.adversaryValue prefixes.adversary.finalState)
        prefixes.adversary.finalCoherent prefixes.verifier.trace prior
        ((queryInput, answer) :: later) decomposition
    rw [if_pos rfl] at countExact
    exact countExact
  have priorCountExact :
      schedulerVerifierRequestCount transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (exactPlainRomCursor configuration sample.1)
            (prefixes.adversary.freshQueries.map Prod.snd))
          (prior.map Prod.snd) = prior.length := by
    rw [scheduler_verifier_request_count_congr transitionFuel _ _ _
      afterAdversaryAligned]
    exact localCount
  have freshCountLeSteps :=
    projected_fresh_returned_trace_answer_count_le_steps
      configuration.machine.verifierLimits .verifier
      configuration.machine.verifierFuel prefixes.adversary.finalState
      (schedulerStageProgram
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (totalizeOracleMachine configuration.machine.verifierFuel
          (initialRawFutureFreeProgram configuration.machine.environment
            prefixes.adversaryValue.rawMessages
            configuration.machine.driverFuel)))
      prefixes.verifier.freshQueries prefixes.verifier.result
      prefixes.verifier.finalState prefixes.verifier.steps
      prefixes.verifier.trace
  have stepsLeFuel := projected_machine_prefix_steps_le_fuel
    configuration.machine.verifierLimits .verifier
    configuration.machine.verifierFuel prefixes.adversary.finalState
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (totalizeOracleMachine configuration.machine.verifierFuel
        (initialRawFutureFreeProgram configuration.machine.environment
          prefixes.adversaryValue.rawMessages
          configuration.machine.driverFuel)))
    prefixes.adversary.remaining prefixes.verifier
  have priorLtFuel : prior.length < configuration.machine.verifierFuel := by
    have priorLtFresh : prior.length < prefixes.verifier.freshQueries.length := by
      rw [decomposition]
      simp
    omega
  refine ⟨?_, globalActor⟩
  rw [scheduler_verifier_request_count_append, adversaryCount,
    zero_add, priorCountExact]
  exact priorLtFuel

/-- Root-only K1.2 tree on the exact compiler master-tape length. -/
def exactK12BudgetedSchedulerTree
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (transitionFuel : Nat) (hidden : HiddenTape) :
    BudgetedCausalTargetTree Digest256 K12RuntimeTargetCap
      (k12RuntimeCaps (exactCompilerTargetCaps parameters).length)
      configuration.machine.verifierFuel :=
  k12BudgetedSchedulerTreeFrom configuration.machine hidden transitionFuel
    (exactCompilerTargetCaps parameters).length
    configuration.machine.verifierFuel []
    (exactPlainRomCursor configuration hidden)

/-- Every concrete unresolved 208-bit Merkle target hit in a completed exact
Tag-73 run is contained in the counted full-output scheduler event. -/
theorem exact_k12_late_target_hit_implies_budgeted_scheduler_hit
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (lateHit : PrefixResolutionLateTargetHit (exactK12Truncate input)
      (exactK12ProverPrefixQueries input) (exactK12OrderedQueries input)
      (exactK12Roots input) (exactK12Openings input)) :
    ((exactK12BudgetedSchedulerTree configuration transitionFuel
      sample.1).toCausal).everHits (k12RuntimeTape sample.2) := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  rcases exact_k12_late_target_hit_has_verifier_fresh_coordinate input lateHit
      with ⟨target, queryInput, answer, prior, later, targetMember,
        decomposition, prefixExact⟩
  obtain ⟨budgetRoom, requestVerifier⟩ :=
    exact_k12_verifier_coordinate_has_budget_and_request transitionRoom input
      queryInput answer prior later decomposition
  let globalPrior := prefixes.adversary.freshQueries.map Prod.snd ++
    prior.map Prod.snd
  let suffix := later.map Prod.snd ++ prefixes.verifier.remaining
  have targetHit : answer ∈ deployedPrefixTargetPreimage
      (k12PrefixTargetsFromAnswers configuration.machine sample.1
        ([] ++ globalPrior)) := by
    simp only [List.nil_append]
    have targetsExact := exact_k12_prefix_targets_from_completed_root input
      (prior.map Prod.snd)
    simp only [deployedPrefixTargetPreimage, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [show globalPrior =
      prefixes.adversary.freshQueries.map Prod.snd ++ prior.map Prod.snd by rfl,
      targetsExact, prefixExact]
    exact targetMember
  have schedulerHit :
      k12SchedulerHitsListFrom configuration.machine sample.1 transitionFuel
        configuration.machine.verifierFuel []
        (exactPlainRomCursor configuration sample.1)
        (globalPrior ++ answer :: suffix) := by
    apply k12_scheduler_hits_list_at_verifier_prefix configuration.machine
      sample.1 transitionFuel (exactPlainRomCursor configuration sample.1) []
      configuration.machine.verifierFuel globalPrior answer suffix
    · exact budgetRoom
    · exact requestVerifier
    · exact targetHit
  have masterExact : freshAnswerTapeToList sample.2 =
      globalPrior ++ answer :: suffix := by
    calc
      freshAnswerTapeToList sample.2 =
          prefixes.adversary.freshQueries.map Prod.snd ++
            prefixes.adversary.remaining :=
        prefixes.adversary.availableExact
      _ = prefixes.adversary.freshQueries.map Prod.snd ++
          (prefixes.verifier.freshQueries.map Prod.snd ++
            prefixes.verifier.remaining) := by
        exact congrArg
          (fun remaining =>
            prefixes.adversary.freshQueries.map Prod.snd ++ remaining)
          prefixes.verifier.availableExact
      _ = globalPrior ++ answer :: suffix := by
        rw [show globalPrior =
          prefixes.adversary.freshQueries.map Prod.snd ++
            prior.map Prod.snd by rfl,
          show suffix = later.map Prod.snd ++
            prefixes.verifier.remaining by rfl,
          decomposition]
        simp only [List.map_append, List.map_cons, List.cons_append,
          List.append_assoc]
  have listHit : budgetedEverHitsList
      (exactK12BudgetedSchedulerTree configuration transitionFuel sample.1)
      (freshAnswerTapeToList sample.2) := by
    have lengthExact : (freshAnswerTapeToList sample.2).length =
        (exactCompilerTargetCaps parameters).length :=
      fresh_answer_tape_to_list_length sample.2
    have schedulerHitOnMaster :
        k12SchedulerHitsListFrom configuration.machine sample.1 transitionFuel
          configuration.machine.verifierFuel []
          (exactPlainRomCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) := by
      rw [masterExact]
      exact schedulerHit
    unfold exactK12BudgetedSchedulerTree
    exact (k12_budgeted_tree_ever_hits_list_iff configuration.machine sample.1
      transitionFuel (exactCompilerTargetCaps parameters).length
      configuration.machine.verifierFuel []
      (exactPlainRomCursor configuration sample.1)
      (freshAnswerTapeToList sample.2) lengthExact).2 schedulerHitOnMaster
  exact (budgeted_ever_hits_iff_ever_hits_list
    (exactK12BudgetedSchedulerTree configuration transitionFuel sample.1)
    (k12RuntimeTape sample.2)).2 (by simpa using listHit)

theorem exact_k12_budgeted_scheduler_tree_probability_le_exact_count
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (transitionFuel : Nat) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (k12RuntimeCaps
          (exactCompilerTargetCaps parameters).length).length).toOuterMeasure
        (hiddenDependentBudgetedRuntimeHitEvent fun hidden =>
          exactK12BudgetedSchedulerTree configuration transitionFuel hidden) ≤
      ((configuration.machine.verifierFuel * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((k12RuntimeCaps
              (exactCompilerTargetCaps parameters).length).length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          (k12RuntimeCaps
            (exactCompilerTargetCaps parameters).length).length) := by
  exact hidden_dependent_budgeted_runtime_probability_le_exact_count hiddenLaw
    (fun hidden =>
      exactK12BudgetedSchedulerTree configuration transitionFuel hidden)

/-- Replace the machine-local verifier fuel by the deployed, source-audited
1,511-call ceiling.  The event and its tree are unchanged. -/
theorem exact_k12_budgeted_scheduler_tree_probability_le_deployed_cap
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (transitionFuel : Nat) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (k12RuntimeCaps
          (exactCompilerTargetCaps parameters).length).length).toOuterMeasure
        (hiddenDependentBudgetedRuntimeHitEvent fun hidden =>
          exactK12BudgetedSchedulerTree configuration transitionFuel hidden) ≤
      ((deployedFull256VerifierCallCap * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((k12RuntimeCaps
              (exactCompilerTargetCaps parameters).length).length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          (k12RuntimeCaps
            (exactCompilerTargetCaps parameters).length).length) := by
  apply (exact_k12_budgeted_scheduler_tree_probability_le_exact_count
    hiddenLaw configuration transitionFuel).trans
  apply ENNReal.div_le_div_right
  have fuelBound := configuration.bounds.rootVerifierFuel
  have coefficientBound :
      configuration.machine.verifierFuel * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((k12RuntimeCaps
              (exactCompilerTargetCaps parameters).length).length - 1) ≤
        deployedFull256VerifierCallCap * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((k12RuntimeCaps
              (exactCompilerTargetCaps parameters).length).length - 1) := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ fuelBound)
  exact_mod_cast coefficientBound

#print axioms k12_prefix_targets_from_answers_card_le
#print axioms k12_runtime_targets_from_answers_card_le
#print axioms projected_fresh_returned_trace_run_machine_append_exact
#print axioms k12_prover_run_from_completed_prefix_append_exact
#print axioms k12_prefix_targets_stable_after_completed_prover
#print axioms projected_machine_prefix_table_extension
#print axioms projected_machine_prefix_lookup_retains_segment_answer
#print axioms lookupEntry_preserved_by_table_extension
#print axioms completed_root_truncate_views_agree_on_prover_history
#print axioms exact_k12_prefix_targets_from_completed_root
#print axioms exact_k12_late_target_hit_has_verifier_fresh_coordinate
#print axioms exact_k12_verifier_coordinate_has_budget_and_request
#print axioms exact_k12_late_target_hit_implies_budgeted_scheduler_hit
#print axioms exact_k12_budgeted_scheduler_tree_probability_le_exact_count
#print axioms exact_k12_budgeted_scheduler_tree_probability_le_deployed_cap

end

end AspisK1.V7Tag73K12BudgetedSchedulerTree
