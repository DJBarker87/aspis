import AspisFormal.K1.V7Tag73ReplayBranchDispatcher
import AspisFormal.K1.V7Tag73StableFirstRunBridge

/-!
# Empty-source Tag-73 replay failure classification

The deployed plain-ROM experiment starts the adversary at the literal empty
oracle.  Consequently the no-pair branch of the generated replay dispatcher
cannot fail because a generated squeeze input was already present in a
caller-supplied initial table.  If the actual first run returned normally,
that branch cannot manufacture a first-run abort or timeout either.

This module proves the resulting exhaustive classification directly from the
executable dispatcher.  In particular, absence of both squeeze inputs from
the frozen first-run query history is handled by the constructed no-pair
replay; it is not charged as a singleton 256-bit prediction.  Remaining
failures are either a concrete atomic-replay failure or the explicit no-pair
resource-budget failure.  No probability, acceptance, or extraction premise
occurs here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73EmptySourceReplayFailure

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73ReplayBranchDispatcher
open AspisK1.V7Tag73StableFirstRunBridge
open AspisK1.V7FsAokExperiment

noncomputable section

/-- Under the literal empty initial oracle and a normally returned first run,
the exhaustive dispatcher has no `firstRun*` or `initialInputConflict`
failure branch.  A missing generated pair is routed to the exact no-pair
replay and can then fail only its stated resource check. -/
theorem empty_returned_source_dispatch_failure_is_atomic_or_no_pair_budget
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    {table : AspisK1.V7Tag73DeterministicRefinement.FixedOracleTable}
    {dag : ConcreteDagInstance}
    (source : EmptyOracleFirstRunSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (configuration : AtomicPairReplayConfiguration)
    (result : Result)
    (returned : source.origin.firstExecution.halt = .returned result)
    (reason : ReplayBranchFailure)
    (failed : dispatchGeneratedReplayBranch source.toSameTapeSource execution
      generated configuration = .error reason) :
    (∃ atomicReason, reason = .atomic atomicReason) ∨
      reason = .noPairResourceBudget := by
  unfold dispatchGeneratedReplayBranch at failed
  split at failed
  · split at failed
    · rename_i occurrenceValue occurrence atomicReason atomicResult
      simp only [Except.error.injEq] at failed
      exact Or.inl ⟨atomicReason, failed.symm⟩
    · contradiction
  · have returned' :
        source.toSameTapeSource.origin.firstExecution.halt =
          .returned result := by
      exact returned
    split at failed
    · exfalso
      simp_all
    · exfalso
      simp_all
    · simp_all only [MachineHalt.returned.injEq]
      simp only [EmptyOracleFirstRunSource.toSameTapeSource, lookupEntry,
        emptyOracle, List.find?_nil] at failed
      split at failed
      · rename_i occurrence returnedValue haltResult noPairReason noPairResult
        simp only [Except.error.injEq] at failed
        unfold constructNoPairReplay at noPairResult
        dsimp only at noPairResult
        split at noPairResult
        · contradiction
        · simp only [Except.error.injEq] at noPairResult
          exact Or.inr (failed.symm.trans noPairResult.symm)
      · contradiction

#print axioms empty_returned_source_dispatch_failure_is_atomic_or_no_pair_budget

end

end AspisK1.V7Tag73EmptySourceReplayFailure
