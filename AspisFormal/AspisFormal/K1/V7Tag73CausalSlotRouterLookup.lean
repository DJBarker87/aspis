import AspisFormal.K1.V7Tag73CausalSlotRouterRealization

/-!
# Lookup semantics for a causal named-slot router

This module packages the one-step routing equations into a recursive lookup.
It lets a protocol-specific trace proof follow one named q16 coordinate
through arbitrary unrelated and residual SHA exposures, while the generic
theorem identifies the eventual answer with the corresponding coordinate of
the measure-preserving equivalence.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalSlotRouterLookup

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterRealization

noncomputable section

/-- Follow one slot name through the adaptive router.  A special step returns
the current answer exactly when it selected `target`; every other step follows
the answer-dependent continuation. -/
def causalRoutedAnswer?
    {Output Slot : Type} [DecidableEq Slot] (target : Slot) :
    {slots : Finset Slot} → {residual : Nat} →
      CausalSlotRouter Output Slot slots residual →
      FreshAnswerTape Output (slots.card + residual) → Option Output
  | _, _, .done, _ => none
  | slots, residual, .special chosen next, tape =>
      let totalEq : slots.card + residual =
          ((slots.erase chosen.1).card + residual) + 1 := by
        rw [Finset.card_erase_of_mem chosen.2]
        have positive : 0 < slots.card :=
          Finset.card_pos.mpr ⟨chosen.1, chosen.2⟩
        omega
      let aligned : Output ×
          FreshAnswerTape Output ((slots.erase chosen.1).card + residual) :=
        castFreshAnswerTape totalEq tape
      if target = chosen.1 then
        some aligned.1
      else
        causalRoutedAnswer? target (next aligned.1) aligned.2
  | slots, remaining + 1, .residual next, tape =>
      let totalEq : slots.card + (remaining + 1) =
          (slots.card + remaining) + 1 := by omega
      let aligned : Output × FreshAnswerTape Output
          (slots.card + remaining) :=
        castFreshAnswerTape totalEq tape
      causalRoutedAnswer? target (next aligned.1) aligned.2

/-- For every still-unfilled named slot, recursive operational lookup is
exactly the value installed by `coordinateEquiv`. -/
theorem routedAnswer?_eq_some_coordinate
    {Output Slot : Type} [DecidableEq Slot]
    {slots : Finset Slot} {residual : Nat}
    (router : CausalSlotRouter Output Slot slots residual)
    (tape : FreshAnswerTape Output (slots.card + residual))
    (target : Slot) (member : target ∈ slots) :
    causalRoutedAnswer? target router tape =
      some ((router.coordinateEquiv tape).1 ⟨target, member⟩) := by
  induction router with
  | done => simp at member
  | @special slots residual chosen next inductionHypothesis =>
      have totalEq : slots.card + residual =
          ((slots.erase chosen.1).card + residual) + 1 := by
        rw [Finset.card_erase_of_mem chosen.2]
        have positive : 0 < slots.card :=
          Finset.card_pos.mpr ⟨chosen.1, chosen.2⟩
        omega
      let aligned : Output ×
          FreshAnswerTape Output ((slots.erase chosen.1).card + residual) :=
        castFreshAnswerTape totalEq tape
      by_cases equal : target = chosen.1
      · have currentEq : (⟨target, member⟩ : ↥slots) = chosen :=
          Subtype.ext equal
        change
          (if target = chosen.1 then some aligned.1
           else causalRoutedAnswer? target (next aligned.1) aligned.2) =
            some (((CausalSlotRouter.special chosen next).coordinateEquiv
              tape).1 ⟨target, member⟩)
        rw [if_pos equal]
        rw [currentEq, special_slot_receives_current_answer]
      · have erasedMember : target ∈ slots.erase chosen.1 :=
          Finset.mem_erase.mpr ⟨equal, member⟩
        have tail := inductionHypothesis aligned.1 aligned.2 erasedMember
        change
          (if target = chosen.1 then some aligned.1
           else causalRoutedAnswer? target (next aligned.1) aligned.2) =
            some (((CausalSlotRouter.special chosen next).coordinateEquiv
              tape).1 ⟨target, member⟩)
        rw [if_neg equal]
        rw [tail]
        apply congrArg some
        symm
        exact special_other_slot_receives_tail_answer chosen
          ⟨target, member⟩ equal next tape
  | @residual slots remaining next inductionHypothesis =>
      have totalEq : slots.card + (remaining + 1) =
          (slots.card + remaining) + 1 := by omega
      let aligned : Output × FreshAnswerTape Output
          (slots.card + remaining) :=
        castFreshAnswerTape totalEq tape
      have tail := inductionHypothesis aligned.1 aligned.2 member
      change
        causalRoutedAnswer? target (next aligned.1) aligned.2 =
          some (((CausalSlotRouter.residual next).coordinateEquiv tape).1
            ⟨target, member⟩)
      rw [tail]
      apply congrArg some
      symm
      exact residual_step_named_slot_receives_tail_answer next tape
        ⟨target, member⟩

/-- Protocol-specific code may prove a lookup equation by following its own
literal execution trace.  This corollary turns that equation directly into
the named-coordinate equality needed by the probability bridge. -/
theorem coordinate_eq_of_causalRoutedAnswer?_eq_some
    {Output Slot : Type} [DecidableEq Slot]
    {slots : Finset Slot} {residual : Nat}
    (router : CausalSlotRouter Output Slot slots residual)
    (tape : FreshAnswerTape Output (slots.card + residual))
    (target : Slot) (member : target ∈ slots) (answer : Output)
    (routed : causalRoutedAnswer? target router tape = some answer) :
    (router.coordinateEquiv tape).1 ⟨target, member⟩ = answer := by
  rw [routedAnswer?_eq_some_coordinate router tape target member] at routed
  exact Option.some.inj routed

#print axioms causalRoutedAnswer?
#print axioms routedAnswer?_eq_some_coordinate
#print axioms coordinate_eq_of_causalRoutedAnswer?_eq_some

end

end AspisK1.V7Tag73CausalSlotRouterLookup
