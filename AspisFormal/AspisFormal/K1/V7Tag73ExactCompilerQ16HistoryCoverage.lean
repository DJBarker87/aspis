import AspisFormal.K1.V7Tag73OperationalSemanticReplay
import AspisFormal.K1.V7Tag73RawVerifierQ16HistoryBridge

/-!
# Exact compiler q16 history coverage

The literal root verifier reconstructed from an exact operational input has
two views of the same run: the scheduler runtime stored in the K1.2 package
and the ordinary `RawVerifierExecution` stored in its projected root.  This
module exposes the q16 facts needed by the source bridge directly on those
objects:

* the completed verifier history is aligned with the future-free q16 control;
* every input/output pair in that history is covered by the exact operational
  first-hit table.

Neither result assigns a role to an adversary query, assumes freshness, or
states the eventual q16 probability conclusion.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerQ16HistoryCoverage

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeQ16HistoryAlignment
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73RawVerifierQ16HistoryBridge

noncomputable section

/-- The chronological verifier-only suffix reconstructed from the literal
projected root execution. -/
def exactOperationalVerifierHistory
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : List QueryRecord :=
  input.package.root.fixedRoot.base.projected.execution.verifierHistory

/-- The actual root verifier's final control and its exact chronological
history satisfy the deployed q16 history automaton invariant. -/
theorem exact_operational_root_has_q16_history_alignment
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
    FutureFreeQ16HistoryAligned
      (exactK12Runtime input).verifierFinalState
      (exactOperationalVerifierHistory input) := by
  let projected := input.package.root.fixedRoot.base.projected
  have aligned :=
    raw_verifier_execution_has_q16_history_alignment projected.execution
  rw [projected.finalStateExact] at aligned
  exact aligned

/-- Every literal pair in the projected root verifier history is an entry of
the exact operational first-hit table.  This is the history-cover premise
consumed by the translated q16 source replay; candidate/squeeze membership is
proved separately from the concrete path shape. -/
theorem exact_operational_verifier_history_is_table_covered
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
    ∀ pair ∈ queryAnswerTrace (exactOperationalVerifierHistory input),
      tableLookup (exactOperationalTable input) pair.1 = some pair.2 := by
  let projected := input.package.root.fixedRoot.base.projected
  obtain ⟨pairs, _path, historyExact, _actors, tableCovered⟩ :=
    raw_verifier_execution_has_exact_query_path projected.execution
  intro pair pairMember
  have pairMember' : pair ∈ pairs := by
    rw [← historyExact]
    exact pairMember
  have covered := tableCovered pair pairMember'
  change tableLookup
      (fixedTableOfOracleState
        input.package.root.fixedRoot.base.runtime.verifierFinalOracle)
      pair.1 = some pair.2
  change tableLookup
      (fixedTableOfOracleState projected.execution.verifierRun.oracle)
      pair.1 = some pair.2 at covered
  rw [projected.finalOracleExact] at covered
  exact covered

#print axioms exactOperationalVerifierHistory
#print axioms exact_operational_root_has_q16_history_alignment
#print axioms exact_operational_verifier_history_is_table_covered

end

end AspisK1.V7Tag73ExactCompilerQ16HistoryCoverage
