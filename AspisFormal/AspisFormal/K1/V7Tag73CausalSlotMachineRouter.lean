import AspisFormal.K1.V7Tag73CausalQ16CoordinateRouter

/-!
# Building a causal coordinate router from a pre-answer machine

`CausalSlotRouter` is the finite measure-preserving object used by the q16
probability bridge.  This file supplies its operational constructor.

A machine state may depend on every answer already exposed.  Before the next
answer is seen, `preferredSlot` may either name one still-relevant special
coordinate or decline to name one.  The constructor routes that answer to the
named coordinate when it is still unfilled.  Every other answer is retained
in the residual tape; if a run halts before all special coordinates occur,
the fixed-length padding tail fills the unused coordinates.  Thus the
constructor is total on every master tape, while a later source-alignment
theorem can show that an accepting run's meaningful coordinates received
their literal protocol labels.

The current answer is never an argument of `preferredSlot`.  The continuation
state may depend on it.  This is the exact nonanticipation boundary needed for
adaptive lazy-oracle scheduling.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CausalSlotMachineRouter

open AspisK1.V7Tag73CausalQ16CoordinateRouter

noncomputable section

universe u

/-- A deterministic pre-answer labelling machine.  Its current label depends
only on the state reached from earlier answers. -/
structure PreAnswerSlotMachine (Output Slot : Type) (State : Type u) where
  preferredSlot : State → Option Slot
  afterAnswer : State → Output → State

/-- One legal destination whenever at least one named or residual coordinate
remains. -/
inductive RemainingDestination
    (Slot : Type) [DecidableEq Slot]
    (slots : Finset Slot) (residual : Nat) where
  | special (chosen : ↥slots)
  | residual (positive : 0 < residual)

/-- Prefer the machine's pre-answer label when it is still unfilled.  All
other answers consume residual coordinates while any remain, followed by a
canonical (choice-only) padding order for unused named coordinates. -/
noncomputable def chooseRemainingDestination
    {Slot : Type} [DecidableEq Slot]
    (slots : Finset Slot) (residual : Nat)
    (remaining : 0 < slots.card + residual)
    (preferred : Option Slot) : RemainingDestination Slot slots residual := by
  classical
  match preferred with
  | some slot =>
      if member : slot ∈ slots then
        exact .special ⟨slot, member⟩
      else if positive : 0 < residual then
        exact .residual positive
      else
        have slotsPositive : 0 < slots.card := by omega
        let witness := Finset.card_pos.mp slotsPositive
        exact .special ⟨Classical.choose witness,
          Classical.choose_spec witness⟩
  | none =>
      if positive : 0 < residual then
        exact .residual positive
      else
        have slotsPositive : 0 < slots.card := by omega
        let witness := Finset.card_pos.mp slotsPositive
        exact .special ⟨Classical.choose witness,
          Classical.choose_spec witness⟩

/-- Compile any pre-answer machine into a complete causal slot router.  The
recursion consumes exactly one named or residual coordinate per answer. -/
noncomputable def PreAnswerSlotMachine.router
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    (machine : PreAnswerSlotMachine Output Slot State) :
    (slots : Finset Slot) → (residual : Nat) → State →
      CausalSlotRouter Output Slot slots residual
  | slots, residual, state => by
      classical
      by_cases remaining : 0 < slots.card + residual
      · cases destination : chooseRemainingDestination slots residual remaining
          (machine.preferredSlot state) with
        | special chosen =>
            exact .special chosen fun answer =>
              machine.router (slots.erase chosen.1) residual
                (machine.afterAnswer state answer)
        | residual positive =>
            cases residual with
            | zero => omega
            | succ remainingResidual =>
                exact .residual fun answer =>
                  machine.router slots remainingResidual
                    (machine.afterAnswer state answer)
      · have emptySlots : slots = ∅ := by
          apply Finset.card_eq_zero.mp
          omega
        have zeroResidual : residual = 0 := by omega
        subst slots
        subst residual
        exact .done
termination_by slots residual _ => slots.card + residual
decreasing_by
  · exact Nat.add_lt_add_right
      (Finset.card_erase_lt_of_mem chosen.2) residual
  · omega

/-- Specialization that fills every member of a finite slot type. -/
noncomputable def PreAnswerSlotMachine.fullRouter
    {Output Slot : Type} {State : Type u} [Fintype Slot] [DecidableEq Slot]
    (machine : PreAnswerSlotMachine Output Slot State)
    (residual : Nat) (state : State) :
    CausalSlotRouter Output Slot Finset.univ residual :=
  machine.router Finset.univ residual state

/-- The compiled machine therefore induces the exact adaptive coordinate
equivalence, with no extra iid or independence premise. -/
noncomputable def PreAnswerSlotMachine.fullCoordinateEquiv
    {Output Slot : Type} {State : Type u} [Fintype Slot] [DecidableEq Slot]
    (machine : PreAnswerSlotMachine Output Slot State)
    (residual : Nat) (state : State) :
    AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape Output
        (Fintype.card Slot + residual) ≃
      (Slot → Output) ×
        AspisK1.V7Tag73AdaptiveLazyOracle.FreshAnswerTape Output residual :=
  (machine.fullRouter residual state).fullCoordinateEquiv

end

#print axioms chooseRemainingDestination
#print axioms PreAnswerSlotMachine.router
#print axioms PreAnswerSlotMachine.fullRouter
#print axioms PreAnswerSlotMachine.fullCoordinateEquiv

end AspisK1.V7Tag73CausalSlotMachineRouter
