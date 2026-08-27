import AspisFormal.K1.V7Tag73CausalSlotMachineRouter

/-!
# Operational realization of causal slot coordinates

The coordinate router is an equivalence, but the protocol bridge also needs
its operational meaning: if the pre-answer machine names a still-unfilled
slot, the current chronological answer is stored in exactly that named
coordinate.  This file proves the one-step kernel lemma used to iterate that
fact over the literal Tag-73 q16 scan.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalSlotRouterRealization

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotMachineRouter

noncomputable section

/-- The first value of a provably nonempty length-indexed answer tape. -/
def freshAnswerTapeHead
    {Output : Type} {steps : Nat}
    (tape : FreshAnswerTape Output steps) (positive : 0 < steps) : Output :=
  match steps with
  | 0 => by omega
  | _ + 1 => tape.1

@[simp] theorem eraseFunctionEquiv_symm_chosen
    {Output Slot : Type} [DecidableEq Slot]
    (slots : Finset Slot) (chosen : ↥slots)
    (answer : Output)
    (remaining : ↥(slots.erase chosen.1) → Output) :
    (eraseFunctionEquiv slots chosen).symm (answer, remaining) chosen = answer := by
  simp [eraseFunctionEquiv]

@[simp] theorem chooseRemainingDestination_some_mem
    {Slot : Type} [DecidableEq Slot]
    (slots : Finset Slot) (residual : Nat)
    (remaining : 0 < slots.card + residual)
    (slot : Slot) (member : slot ∈ slots) :
    chooseRemainingDestination slots residual remaining (some slot) =
      RemainingDestination.special ⟨slot, member⟩ := by
  simp [chooseRemainingDestination, member]

theorem router_eq_special_of_choice
    {Output Slot State : Type} [DecidableEq Slot]
    (machine : PreAnswerSlotMachine Output Slot State)
    (slots : Finset Slot) (residual : Nat) (state : State)
    (remaining : 0 < slots.card + residual)
    (chosen : ↥slots)
    (choice : chooseRemainingDestination slots residual remaining
        (machine.preferredSlot state) =
      RemainingDestination.special chosen) :
    machine.router slots residual state =
      CausalSlotRouter.special chosen (fun answer =>
        machine.router (slots.erase chosen.1) residual
          (machine.afterAnswer state answer)) := by
  rw [PreAnswerSlotMachine.router.eq_def]
  simp only [dif_pos remaining]
  rw [choice]

/-- The named coordinate chosen by a special router step is exactly the
current chronological answer.  This is the small kernel fact beneath the
machine-level realization theorem. -/
theorem special_slot_receives_current_answer
    {Output Slot : Type} [DecidableEq Slot]
    {slots : Finset Slot} {residual : Nat}
    (chosen : ↥slots)
    (next : Output → CausalSlotRouter Output Slot
      (slots.erase chosen.1) residual)
    (tape : FreshAnswerTape Output (slots.card + residual)) :
    ((CausalSlotRouter.special chosen next).coordinateEquiv tape).1 chosen =
      (castFreshAnswerTape (by
          have cardErase : (slots.erase chosen.1).card = slots.card - 1 :=
            Finset.card_erase_of_mem chosen.2
          have cardPositive : 0 < slots.card :=
            Finset.card_pos.mpr ⟨chosen.1, chosen.2⟩
          omega : slots.card + residual =
            ((slots.erase chosen.1).card + residual) + 1) tape :
        FreshAnswerTape Output
          (((slots.erase chosen.1).card + residual) + 1)).1 := by
  classical
  have totalEq : slots.card + residual =
      ((slots.erase chosen.1).card + residual) + 1 := by
    rw [Finset.card_erase_of_mem chosen.2]
    have positive : 0 < slots.card :=
      Finset.card_pos.mpr ⟨chosen.1, chosen.2⟩
    omega
  let aligned := castFreshAnswerTape totalEq tape
  change
    (eraseFunctionEquiv slots chosen).symm
        (aligned.1, ((next aligned.1).coordinateEquiv aligned.2).1) chosen =
      aligned.1
  exact eraseFunctionEquiv_symm_chosen slots chosen aligned.1
    ((next aligned.1).coordinateEquiv aligned.2).1

/-- When the pre-answer machine names a slot that is still unfilled, its
compiled router takes the special branch and stores the current answer in
that slot.  The decision uses only the state preceding the answer. -/
theorem machine_preferred_slot_receives_current_answer
    {Output Slot State : Type} [DecidableEq Slot]
    (machine : PreAnswerSlotMachine Output Slot State)
    (slots : Finset Slot) (residual : Nat) (state : State)
    (slot : Slot) (member : slot ∈ slots)
    (preferred : machine.preferredSlot state = some slot)
    (tape : FreshAnswerTape Output (slots.card + residual)) :
    ((machine.router slots residual state).coordinateEquiv tape).1
        ⟨slot, member⟩ =
      (castFreshAnswerTape (by
          rw [Finset.card_erase_of_mem member]
          have positive : 0 < slots.card :=
            Finset.card_pos.mpr ⟨slot, member⟩
          omega : slots.card + residual =
            ((slots.erase slot).card + residual) + 1) tape :
        FreshAnswerTape Output
          (((slots.erase slot).card + residual) + 1)).1 := by
  classical
  have remaining : 0 < slots.card + residual := by
    have positive : 0 < slots.card := Finset.card_pos.mpr ⟨slot, member⟩
    omega
  have choice :
      chooseRemainingDestination slots residual remaining
          (machine.preferredSlot state) =
        RemainingDestination.special ⟨slot, member⟩ := by
    rw [preferred]
    exact chooseRemainingDestination_some_mem slots residual remaining slot member
  rw [router_eq_special_of_choice machine slots residual state remaining
    ⟨slot, member⟩ choice]
  exact special_slot_receives_current_answer
      (chosen := ⟨slot, member⟩)
      (next := fun answer =>
        machine.router (slots.erase slot) residual
          (machine.afterAnswer state answer))
      tape

#print axioms special_slot_receives_current_answer
#print axioms machine_preferred_slot_receives_current_answer

end

end AspisK1.V7Tag73CausalSlotRouterRealization
