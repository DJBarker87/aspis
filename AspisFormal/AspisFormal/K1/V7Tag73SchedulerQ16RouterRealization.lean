import AspisFormal.K1.V7Tag73CausalSlotRouterRealization
import AspisFormal.K1.V7Tag73SchedulerHistoryQ16Router

/-!
# Operational realization of the scheduler-history q16 router

The exact plain-ROM router is driven by the unified scheduler cursor.  This
module instantiates the generic one-step routing theorem: whenever the
completed root-verifier history names a still-unfilled q16 coordinate before
the current SHA answer is exposed, that answer occupies exactly the named
coordinate in the induced measure-preserving map.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73SchedulerQ16RouterRealization

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterRealization
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerHistoryQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- One exact scheduler-history label has its literal operational meaning in
the compiled causal router.  The label is a pre-answer equality; the current
digest appears only in `tape.1`. -/
theorem scheduler_history_label_receives_current_answer
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (slots : Finset Q16DigestSlot) (residual : Nat)
    (slot : Q16DigestSlot) (member : slot ∈ slots)
    (labelExact : schedulerHistoryQ16Label transitionFuel cursor = some slot)
    (tape : FreshAnswerTape Digest256 (slots.card + residual)) :
    (((unifiedExposureSlotMachine transitionFuel
          (schedulerHistoryQ16Label transitionFuel)).router
        slots residual cursor).coordinateEquiv tape).1 ⟨slot, member⟩ =
      (castFreshAnswerTape (by
          rw [Finset.card_erase_of_mem member]
          have positive : 0 < slots.card :=
            Finset.card_pos.mpr ⟨slot, member⟩
          omega : slots.card + residual =
            ((slots.erase slot).card + residual) + 1) tape :
        FreshAnswerTape Digest256
          (((slots.erase slot).card + residual) + 1)).1 := by
  have preferred :
      (unifiedExposureSlotMachine transitionFuel
          (schedulerHistoryQ16Label transitionFuel)).preferredSlot cursor =
        some slot := by
    simpa [unifiedExposureSlotMachine] using labelExact
  simpa only [unifiedExposureSlotMachine] using
    (machine_preferred_slot_receives_current_answer
      (unifiedExposureSlotMachine transitionFuel
        (schedulerHistoryQ16Label transitionFuel))
      slots residual cursor slot member preferred tape)

#print axioms scheduler_history_label_receives_current_answer

end

end AspisK1.V7Tag73SchedulerQ16RouterRealization
