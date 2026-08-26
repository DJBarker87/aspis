import AspisFormal.K1.V7Tag73K12Merkle208PrefixProjection
import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal
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
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73UniformRawVerifierExecution
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ProjectedFreshController
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
#print axioms exact_k12_budgeted_scheduler_tree_probability_le_exact_count
#print axioms exact_k12_budgeted_scheduler_tree_probability_le_deployed_cap

end

end AspisK1.V7Tag73K12BudgetedSchedulerTree
