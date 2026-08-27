import AspisFormal.K1.V7Tag73FutureFreeQ16HistoryAlignment

/-!
# Exact q16 pre-answer label from aligned verifier history

The scheduler's causal router reads only the completed SHA history.  When the
literal future-free verifier is at a bounded q16 output exposure, the history
automaton names exactly the same candidate/block slot as the operational
control state.  The current digest answer is not an input to either label.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73Q16HistoryLabelExact

open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73Q16ControlInvariant
open AspisK1.V7Tag73FutureFreeQ16ExposureMachine
open AspisK1.V7Tag73SchedulerHistoryQ16Router
open AspisK1.V7Tag73FutureFreeQ16HistoryAlignment

noncomputable section

/-- At a live bounded q16 sampler, the history-only pre-answer label is the
literal operational candidate/block slot. -/
theorem aligned_history_labels_exact_q16_slot
    (state : FutureFreeVerifierState) (history : List QueryRecord)
    (base : Digest256) (counter : Fin 64) (outputs : List Digest256)
    (remaining : List FutureFreeSlot) (digest : Digest256)
    (controlExact : state.current.control =
      .q16Sample base counter outputs remaining)
    (bounded : Q16SnapshotSlotBound state.current)
    (aligned : FutureFreeQ16HistoryAligned state history) :
    rootQ16PreferredSlotFromHistory history
        (bytes digest ++ [domSqueeze]) =
      some (q16DigestSlotOfBoundedSnapshot state.current base counter outputs
        remaining controlExact bounded) := by
  have phaseExact : rootQ16HistoryPhase history =
      .ready counter outputs.length := by
    simpa [FutureFreeQ16HistoryAligned, controlExact] using aligned
  have outputBound : outputs.length < 8 := by
    rw [Q16SnapshotSlotBound, controlExact] at bounded
    exact bounded
  rw [root_q16_preferred_slot_of_ready_phase history counter outputs.length
    digest phaseExact outputBound]
  apply congrArg some
  apply Prod.ext
  · rfl
  · apply Fin.ext
    rfl

#print axioms aligned_history_labels_exact_q16_slot

end

end AspisK1.V7Tag73Q16HistoryLabelExact
