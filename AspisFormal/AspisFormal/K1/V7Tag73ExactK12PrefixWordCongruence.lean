import AspisFormal.K1.V7Tag73K12BudgetedSchedulerTree
import AspisFormal.Pool.V7MerklePrefixTargetCongruence

/-!
# Exact K1.2 prefix-word congruence

The K1.2 word extractor is written against the verifier-final total hash
view, but its deterministic partial-path completion only reads values from
the completed prover prefix.  This module turns equality of two exact prover
runtimes into equality of the extracted K1.2 words, without requiring their
later verifier-final tables to be equal.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactK12PrefixWordCongruence

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisPool.V7MerklePrefixTargetCongruence
open AspisPool.V7MerklePartialPathExtractor

noncomputable section

/-- Expose the literal runtime packaged by one exact accepted root. -/
theorem exact_k12_runtime_eq_root_projection
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    let prefixes := input.package.root.full.projection.rootPrefixes
    exactK12Runtime input =
      operationalRootRuntime (configuration.machine.tapeIdentity sample.1)
        prefixes.adversaryValue prefixes.adversary.finalState
        prefixes.verifier.finalState prefixes.verifierFinalStateValue := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  simpa [exactK12Runtime, prefixes] using prefixes.runtimeExact

/-- Although the classifier is parameterized by the verifier-final hash view,
it agrees with the prover-final view on every raw input in its fixed prefix
log. -/
theorem exact_k12_truncate_eq_prover_truncate_on_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∀ rawInput ∈ exactK12ProverPrefixQueries input,
      exactK12Truncate input rawInput =
        truncateAtOracleState (exactK12Runtime input).proverFinalOracle rawInput := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have runtimeExact := exact_k12_runtime_eq_root_projection input
  have truncateExact : exactK12Truncate input =
      truncateAtOracleState prefixes.verifier.finalState := by
    funext rawInput
    unfold exactK12Truncate truncateAtOracleState
    rw [runtimeExact]
    rfl
  have prefixLogExact : exactK12ProverPrefixQueries input =
      prefixes.adversary.finalState.history.map
        (fun record : QueryRecord => runtimeInputToRawHashInput record.input) := by
    unfold exactK12ProverPrefixQueries
    rw [runtimeExact]
    rfl
  have proverExact : (exactK12Runtime input).proverFinalOracle =
      prefixes.adversary.finalState := by
    rw [runtimeExact]
    rfl
  intro rawInput member
  rw [prefixLogExact] at member
  calc
    exactK12Truncate input rawInput =
        truncateAtOracleState prefixes.verifier.finalState rawInput := by
          rw [truncateExact]
    _ = truncateAtOracleState prefixes.adversary.finalState rawInput := by
      exact (completed_root_truncate_views_agree_on_prover_history
        configuration.machine sample.1 (freshAnswerTapeToList sample.2)
        input.package.root.fixedRoot.base.runtime prefixes rawInput member).symm
    _ = truncateAtOracleState (exactK12Runtime input).proverFinalOracle rawInput := by
      rw [proverExact]

/-- Equal returned proof values and equal prover-final oracle states force
the exact K1.2 fixed-prefix completion to be identical.  Later verifier
queries may differ; the proof only uses their agreement with the retained
prover state on the finite prefix log. -/
theorem exact_prefix_k12_words_eq_of_same_prover_runtime
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (adversaryExact : (exactK12Runtime left).adversaryValue =
      (exactK12Runtime right).adversaryValue)
    (proverExact : (exactK12Runtime left).proverFinalOracle =
      (exactK12Runtime right).proverFinalOracle) :
    exactPrefixK12Words left = exactPrefixK12Words right := by
  have rootsExact : exactK12Roots left = exactK12Roots right := by
    unfold exactK12Roots
    rw [adversaryExact]
  have logsExact : exactK12ProverPrefixQueries left =
      exactK12ProverPrefixQueries right := by
    unfold exactK12ProverPrefixQueries
    rw [proverExact]
  have truncateAgree : ∀ rawInput ∈ exactK12ProverPrefixQueries left,
      exactK12Truncate left rawInput = exactK12Truncate right rawInput := by
    intro rawInput rawMember
    have leftExact := exact_k12_truncate_eq_prover_truncate_on_prefix left
      rawInput rawMember
    have rightMember : rawInput ∈ exactK12ProverPrefixQueries right := by
      rw [← logsExact]
      exact rawMember
    have rightExact := exact_k12_truncate_eq_prover_truncate_on_prefix right
      rawInput rightMember
    calc
      exactK12Truncate left rawInput =
          truncateAtOracleState (exactK12Runtime left).proverFinalOracle rawInput :=
        leftExact
      _ = truncateAtOracleState (exactK12Runtime right).proverFinalOracle rawInput := by
        rw [proverExact]
      _ = exactK12Truncate right rawInput := rightExact.symm
  unfold exactPrefixK12Words
  calc
    extractPrefixFixedWords (exactK12Truncate left)
        (exactK12ProverPrefixQueries left) (exactK12Roots left) =
      extractPrefixFixedWords (exactK12Truncate right)
        (exactK12ProverPrefixQueries left) (exactK12Roots left) :=
      extractPrefixFixedWords_eq_of_agree_on_log (exactK12Truncate left)
        (exactK12Truncate right) (exactK12ProverPrefixQueries left)
          truncateAgree (exactK12Roots left)
    _ = extractPrefixFixedWords (exactK12Truncate right)
        (exactK12ProverPrefixQueries right) (exactK12Roots right) := by
      rw [logsExact, rootsExact]

#print axioms exact_k12_runtime_eq_root_projection
#print axioms exact_k12_truncate_eq_prover_truncate_on_prefix
#print axioms exact_prefix_k12_words_eq_of_same_prover_runtime

end

end AspisK1.V7Tag73ExactK12PrefixWordCongruence
