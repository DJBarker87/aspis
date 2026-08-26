import AspisFormal.K1.V7Tag73K12Merkle208PrefixProjection
import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal
import AspisFormal.K1.V7Tag73CompletedRootProjection
import AspisFormal.Pool.V7MerklePartialPathExtractor

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
open AspisK1.V7BudgetedAdaptiveTargets
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73K12Merkle208CollisionProbability
open AspisK1.V7Tag73K12Merkle208PrefixProjection
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerklePartialPathExtractor

noncomputable section

abbrev K12RuntimeTargetCap : Nat :=
  prefixFixedResolutionTargetCap * 2 ^ 48

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
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Tag73K12ParsedProof Payload)
    (prefixes : CompletedRootProjectedPrefixes machine hidden available runtime)
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
      (RootSchedulerResult TapeIdentity Statement Tag73K12ParsedProof Payload)
      (totalizeOracleMachine machine.adversaryFuel
        (machine.blackBox.start hidden machine.observation)))
    prefixes.adversary.freshQueries prefixes.adversary.result
    prefixes.adversary.finalState prefixes.adversary.steps
    empty_oracle_history_total_coherent prefixes.adversary.trace tail
  rw [prefixes.adversaryResult] at wrapped
  have totalized := run_machine_scheduler_stage_completed_reflects
    (Final := RootSchedulerResult TapeIdentity Statement Tag73K12ParsedProof
      Payload)
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
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (available : List Digest256)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Tag73K12ParsedProof Payload)
    (prefixes : CompletedRootProjectedPrefixes machine hidden available runtime)
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

def schedulerNativeRequestActor?
    {globalOracleCalls : Nat} {Result : Type} :
    SchedulerNativeRequest globalOracleCalls Result → Option QueryActor
  | .machineFresh _limits _limitBound actor _state _input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
      some actor
  | .returned _ | .failed _ | .transitionLimit | .forkOutput .. |
      .forkAdvance .. => none

/-- Follow the root cursor for a fixed number of padded master coordinates.
The budget index is consumed only by literal root-verifier fresh requests.
If a malformed execution somehow reaches another verifier request after the
supplied budget is exhausted, that coordinate is left free; the operational
fuel lemma rules this branch out for completed exact inputs. -/
def k12BudgetedSchedulerTreeFrom
    {HiddenTape TapeIdentity Observation Statement Payload : Type}
    {globalOracleCalls : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Tag73K12ParsedProof Payload)
    (hidden : HiddenTape) (transitionFuel : Nat) :
    (remaining budget : Nat) → List Digest256 →
      SchedulerNativeCursor globalOracleCalls
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload PUnit) →
      BudgetedCausalTargetTree Digest256 K12RuntimeTargetCap
        (List.replicate remaining K12RuntimeTargetCap) budget
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

/-- Root-only K1.2 tree on the exact compiler master-tape length. -/
def exactK12BudgetedSchedulerTree
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (transitionFuel : Nat) (hidden : HiddenTape) :
    BudgetedCausalTargetTree Digest256 K12RuntimeTargetCap
      (List.replicate (exactCompilerTargetCaps parameters).length
        K12RuntimeTargetCap)
      configuration.machine.verifierFuel :=
  k12BudgetedSchedulerTreeFrom configuration.machine hidden transitionFuel
    (exactCompilerTargetCaps parameters).length
    configuration.machine.verifierFuel []
    (exactPlainRomRootCursor configuration hidden)

theorem exact_k12_budgeted_scheduler_tree_probability_le_exact_count
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (transitionFuel : Nat) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw
        (List.replicate (exactCompilerTargetCaps parameters).length
          K12RuntimeTargetCap).length).toOuterMeasure
        (hiddenDependentBudgetedRuntimeHitEvent fun hidden =>
          exactK12BudgetedSchedulerTree configuration transitionFuel hidden) ≤
      ((configuration.machine.verifierFuel * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((List.replicate (exactCompilerTargetCaps parameters).length
              K12RuntimeTargetCap).length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          (List.replicate (exactCompilerTargetCaps parameters).length
            K12RuntimeTargetCap).length) := by
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
        (List.replicate (exactCompilerTargetCaps parameters).length
          K12RuntimeTargetCap).length).toOuterMeasure
        (hiddenDependentBudgetedRuntimeHitEvent fun hidden =>
          exactK12BudgetedSchedulerTree configuration transitionFuel hidden) ≤
      ((deployedFull256VerifierCallCap * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((List.replicate (exactCompilerTargetCaps parameters).length
              K12RuntimeTargetCap).length - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^
          (List.replicate (exactCompilerTargetCaps parameters).length
            K12RuntimeTargetCap).length) := by
  apply (exact_k12_budgeted_scheduler_tree_probability_le_exact_count
    hiddenLaw configuration transitionFuel).trans
  apply ENNReal.div_le_div_right
  have fuelBound := configuration.bounds.rootVerifierFuel
  have coefficientBound :
      configuration.machine.verifierFuel * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((List.replicate (exactCompilerTargetCaps parameters).length
              K12RuntimeTargetCap).length - 1) ≤
        deployedFull256VerifierCallCap * K12RuntimeTargetCap *
          (2 ^ 256) ^
            ((List.replicate (exactCompilerTargetCaps parameters).length
              K12RuntimeTargetCap).length - 1) := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ fuelBound)
  exact_mod_cast coefficientBound

#print axioms k12_prefix_targets_from_answers_card_le
#print axioms k12_runtime_targets_from_answers_card_le
#print axioms projected_fresh_returned_trace_run_machine_append_exact
#print axioms k12_prover_run_from_completed_prefix_append_exact
#print axioms k12_prefix_targets_stable_after_completed_prover
#print axioms exact_k12_budgeted_scheduler_tree_probability_le_exact_count
#print axioms exact_k12_budgeted_scheduler_tree_probability_le_deployed_cap

end

end AspisK1.V7Tag73K12BudgetedSchedulerTree
