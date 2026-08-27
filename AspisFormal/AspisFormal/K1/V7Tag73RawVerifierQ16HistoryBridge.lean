import AspisFormal.K1.V7Tag73RawVerifierExecution
import AspisFormal.K1.V7Tag73FutureFreeQ16HistoryAlignment

/-!
# Literal verifier execution preserves q16 history alignment

The causal q16 router reads the completed root-verifier SHA history.  This
module connects that history to one actual normally returned Tag-73 verifier
execution: the actor-rich records realize the exact actor-free query path, so
the operational trace invariant identifies every live q16 sampler with the
literal next candidate/block coordinate.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawVerifierQ16HistoryBridge

open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawVerifierExecution
open AspisK1.V7Tag73FutureFreeQ16HistoryAlignment

noncomputable section

/-- Every normally returned literal verifier run finishes with its live q16
control state aligned to the exact chronological root-verifier SHA history.
No acceptance, probability, decoder, or source-correspondence premise is
used. -/
theorem raw_verifier_execution_has_q16_history_alignment
    {HiddenTape TapeIdentity Observation Statement Proof Payload : Type*}
    {source : RawTag73SameTapeSource HiddenTape TapeIdentity Observation
      Statement Proof Payload}
    (execution : RawVerifierExecution source) :
    FutureFreeQ16HistoryAligned execution.finalState
      execution.verifierHistory := by
  obtain ⟨pairs, path, historyExact, actors, _answers⟩ :=
    raw_verifier_execution_has_exact_query_path execution
  have trace : FutureFreeOperationalTrace execution.environment
      execution.adversaryValue.rawMessages
      (initialFutureFreeVerifierState
        (FixedBindings.ofContext execution.adversaryValue.rawMessages.context))
      pairs execution.finalState :=
    initial_raw_future_free_path_is_operational_trace execution.environment
      execution.adversaryValue.rawMessages execution.driverFuel pairs
      execution.finalState path
  have realized : VerifierRecordsRealizePairs execution.verifierHistory pairs :=
    ⟨historyExact, actors⟩
  have aligned :=
    future_free_operational_trace_preserves_q16_history_alignment
      execution.environment execution.adversaryValue.rawMessages
      (initialFutureFreeVerifierState
        (FixedBindings.ofContext execution.adversaryValue.rawMessages.context))
      execution.finalState pairs execution.verifierHistory [] trace realized
      (initial_future_free_q16_history_aligned
        (FixedBindings.ofContext execution.adversaryValue.rawMessages.context)
        [])
  simpa using aligned

#print axioms raw_verifier_execution_has_q16_history_alignment

end

end AspisK1.V7Tag73RawVerifierQ16HistoryBridge
