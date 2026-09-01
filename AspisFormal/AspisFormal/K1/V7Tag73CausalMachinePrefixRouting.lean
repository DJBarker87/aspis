import AspisFormal.K1.V7Tag73CausalSlotRouterLookup

/-!
# Prefix semantics of a compiled pre-answer router

This is the generic induction used by the Tag-73 source cover.  It follows an
actual prefix of answers through `PreAnswerSlotMachine.router`, retaining the
remaining named slots, residual capacity, controller state, and untouched
answer tail.  A named coordinate that remains live is unchanged by the
prefix.  If the controller then names it, the recursive routed lookup is the
literal next answer.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalMachinePrefixRouting

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73CausalSlotRouterRealization

noncomputable section

universe u

theorem specialStepLengthEq
    {Slot : Type} [DecidableEq Slot]
    (slots : Finset Slot) (residual : Nat) (chosen : ↥slots) :
    slots.card + residual =
      ((slots.erase chosen.1).card + residual) + 1 := by
  rw [Finset.card_erase_of_mem chosen.2]
  have positive : 0 < slots.card :=
    Finset.card_pos.mpr ⟨chosen.1, chosen.2⟩
  omega

theorem residualStepLengthEq
    (slotCount remaining : Nat) :
    slotCount + (remaining + 1) = (slotCount + remaining) + 1 := by
  omega

/-- Proof-relevant execution of a finite answer prefix through the exact
compiled router.  Every constructor records the router's actual pre-answer
choice and the proof-indexed head/tail split of the chronological tape. -/
inductive MachineRouterPrefix
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    (machine : PreAnswerSlotMachine Output Slot State) :
    {slots : Finset Slot} → {residual : Nat} → State →
      FreshAnswerTape Output (slots.card + residual) →
      {remainingSlots : Finset Slot} → {remainingResidual : Nat} →
      State → FreshAnswerTape Output
        (remainingSlots.card + remainingResidual) → Prop where
  | refl (slots : Finset Slot) (residual : Nat) (state : State)
      (tape : FreshAnswerTape Output (slots.card + residual)) :
      MachineRouterPrefix machine state tape state tape
  | special
      {slots : Finset Slot} {residual : Nat} {state : State}
      (remaining : 0 < slots.card + residual) (chosen : ↥slots)
      (choice : chooseRemainingDestination slots residual remaining
        (machine.preferredSlot state) = .special chosen)
      (tape : FreshAnswerTape Output (slots.card + residual))
      (answer : Output)
      (tail : FreshAnswerTape Output
        ((slots.erase chosen.1).card + residual))
      (tapeExact : castFreshAnswerTape
        (specialStepLengthEq slots residual chosen) tape = (answer, tail))
      {remainingSlots : Finset Slot} {remainingResidual : Nat}
      {remainingState : State}
      {remainingTape : FreshAnswerTape Output
        (remainingSlots.card + remainingResidual)}
      (rest : MachineRouterPrefix machine
        (slots := slots.erase chosen.1) (residual := residual)
        (machine.afterAnswer state answer) tail
        (remainingSlots := remainingSlots)
        (remainingResidual := remainingResidual)
        remainingState remainingTape) :
      MachineRouterPrefix machine state tape remainingState remainingTape
  | residual
      {slots : Finset Slot} {remainingResidual : Nat} {state : State}
      (remaining : 0 < slots.card + (remainingResidual + 1))
      (choice : chooseRemainingDestination slots (remainingResidual + 1)
        remaining (machine.preferredSlot state) = .residual (by omega))
      (tape : FreshAnswerTape Output
        (slots.card + (remainingResidual + 1)))
      (answer : Output)
      (tail : FreshAnswerTape Output (slots.card + remainingResidual))
      (tapeExact : castFreshAnswerTape
        (residualStepLengthEq slots.card remainingResidual) tape =
          (answer, tail))
      {finalSlots : Finset Slot} {finalResidual : Nat}
      {finalState : State}
      {finalTape : FreshAnswerTape Output
        (finalSlots.card + finalResidual)}
      (rest : MachineRouterPrefix machine
        (slots := slots) (residual := remainingResidual)
        (machine.afterAnswer state answer) tail
        (remainingSlots := finalSlots)
        (remainingResidual := finalResidual) finalState finalTape) :
      MachineRouterPrefix machine state tape finalState finalTape

/-- A prefix can only erase named slots; it never introduces one. -/
theorem machine_router_prefix_remaining_subset
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    {machine : PreAnswerSlotMachine Output Slot State}
    {slots remainingSlots : Finset Slot} {residual remainingResidual : Nat}
    {state remainingState : State}
    {tape : FreshAnswerTape Output (slots.card + residual)}
    {remainingTape : FreshAnswerTape Output
      (remainingSlots.card + remainingResidual)}
    (route : MachineRouterPrefix machine state tape remainingState
      remainingTape) :
    remainingSlots ⊆ slots := by
  induction route with
  | refl => exact fun _ member => member
  | special remaining chosen choice tape answer tail tapeExact rest ih =>
      exact ih.trans (Finset.erase_subset chosen.1 _)
  | residual remaining choice tape answer tail tapeExact rest ih =>
      exact ih

theorem router_eq_residual_of_choice
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    (machine : PreAnswerSlotMachine Output Slot State)
    (slots : Finset Slot) (remainingResidual : Nat) (state : State)
    (remaining : 0 < slots.card + (remainingResidual + 1))
    (choice : chooseRemainingDestination slots (remainingResidual + 1)
        remaining (machine.preferredSlot state) = .residual (by omega)) :
    machine.router slots (remainingResidual + 1) state =
      CausalSlotRouter.residual (fun answer =>
        machine.router slots remainingResidual
          (machine.afterAnswer state answer)) := by
  rw [PreAnswerSlotMachine.router.eq_def]
  simp only [dif_pos remaining]
  rw [choice]

/-- Every named coordinate that survives a routed prefix retains exactly the
value obtained by recursively routing the untouched tail. -/
theorem machine_router_prefix_preserves_named_coordinate
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    {machine : PreAnswerSlotMachine Output Slot State}
    {slots remainingSlots : Finset Slot} {residual remainingResidual : Nat}
    {state remainingState : State}
    {tape : FreshAnswerTape Output (slots.card + residual)}
    {remainingTape : FreshAnswerTape Output
      (remainingSlots.card + remainingResidual)}
    (route : MachineRouterPrefix machine state tape remainingState
      remainingTape)
    (target : Slot) (initialMember : target ∈ slots)
    (remainingMember : target ∈ remainingSlots) :
    ((machine.router slots residual state).coordinateEquiv tape).1
        ⟨target, initialMember⟩ =
      ((machine.router remainingSlots remainingResidual
          remainingState).coordinateEquiv remainingTape).1
        ⟨target, remainingMember⟩ := by
  induction route with
  | refl => rfl
  | @special slots residual state remaining chosen choice tape answer tail
      tapeExact finalSlots finalResidual finalState finalTape rest ih =>
      have tailMember : target ∈ slots.erase chosen.1 :=
        machine_router_prefix_remaining_subset rest remainingMember
      have different : target ≠ chosen.1 := (Finset.mem_erase.mp tailMember).1
      rw [router_eq_special_of_choice machine slots residual state remaining
        chosen choice]
      calc
        ((CausalSlotRouter.special chosen (fun current =>
              machine.router (slots.erase chosen.1) residual
                (machine.afterAnswer state current))).coordinateEquiv tape).1
            ⟨target, initialMember⟩ =
            ((machine.router (slots.erase chosen.1) residual
                (machine.afterAnswer state answer)).coordinateEquiv tail).1
              ⟨target, tailMember⟩ := by
                rw [special_other_slot_receives_tail_answer chosen
                  ⟨target, initialMember⟩ different]
                rw [tapeExact]
        _ = ((machine.router finalSlots finalResidual
                finalState).coordinateEquiv finalTape).1
              ⟨target, remainingMember⟩ :=
            ih tailMember remainingMember
  | @residual slots priorResidual state remaining choice tape answer tail
      tapeExact finalSlots finalResidual finalState finalTape rest ih =>
      have tailMember : target ∈ slots :=
        machine_router_prefix_remaining_subset rest remainingMember
      rw [router_eq_residual_of_choice machine slots priorResidual state
        remaining choice]
      calc
        ((CausalSlotRouter.residual (fun current =>
              machine.router slots priorResidual
                (machine.afterAnswer state current))).coordinateEquiv tape).1
            ⟨target, initialMember⟩ =
            ((machine.router slots priorResidual
                (machine.afterAnswer state answer)).coordinateEquiv tail).1
              ⟨target, tailMember⟩ := by
                rw [residual_step_named_slot_receives_tail_answer]
                rw [tapeExact]
        _ = ((machine.router finalSlots finalResidual
                finalState).coordinateEquiv finalTape).1
              ⟨target, remainingMember⟩ :=
            ih tailMember remainingMember

/-- Final operational form.  After an arbitrary certified prefix, if the
pre-answer controller names a still-live target, its recursive lookup in the
original router is exactly the literal next chronological answer. -/
theorem machine_router_prefix_then_preferred_routed_answer
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    {machine : PreAnswerSlotMachine Output Slot State}
    {slots remainingSlots : Finset Slot} {residual remainingResidual : Nat}
    {state remainingState : State}
    {tape : FreshAnswerTape Output (slots.card + residual)}
    {remainingTape : FreshAnswerTape Output
      (remainingSlots.card + remainingResidual)}
    (route : MachineRouterPrefix machine state tape remainingState
      remainingTape)
    (target : Slot) (remainingMember : target ∈ remainingSlots)
    (preferred : machine.preferredSlot remainingState = some target)
    (answer : Output)
    (tail : FreshAnswerTape Output
      ((remainingSlots.erase target).card + remainingResidual))
    (tapeExact : castFreshAnswerTape
      (specialStepLengthEq remainingSlots remainingResidual
        ⟨target, remainingMember⟩) remainingTape = (answer, tail)) :
    causalRoutedAnswer? target (machine.router slots residual state) tape =
      some answer := by
  have initialMember : target ∈ slots :=
    machine_router_prefix_remaining_subset route remainingMember
  rw [routedAnswer?_eq_some_coordinate
    (machine.router slots residual state) tape target initialMember]
  apply congrArg some
  rw [machine_router_prefix_preserves_named_coordinate route target
    initialMember remainingMember]
  rw [machine_preferred_slot_receives_current_answer machine remainingSlots
    remainingResidual remainingState target remainingMember preferred]
  rw [tapeExact]

#print axioms MachineRouterPrefix
#print axioms machine_router_prefix_remaining_subset
#print axioms router_eq_residual_of_choice
#print axioms machine_router_prefix_preserves_named_coordinate
#print axioms machine_router_prefix_then_preferred_routed_answer

end

end AspisK1.V7Tag73CausalMachinePrefixRouting
