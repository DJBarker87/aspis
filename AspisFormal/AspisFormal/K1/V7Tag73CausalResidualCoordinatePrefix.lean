import AspisFormal.K1.V7Tag73CausalMachineLabeledTraceRouting

/-!
# Residual-coordinate prefix semantics for causal slot routers

The final-work/q16 compiler equivalence reserves 513 named coordinates and
returns every other chronological SHA answer as one residual tape.  This
generic leaf records the converse operational fact needed by the source
noninterference bridge: a residual router step exposes the literal head in
the residual component, and equality of residual components therefore fixes
all earlier residual-only answers.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalResidualCoordinatePrefix

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalMachinePrefixRouting
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73OperationalOracleExposure

noncomputable section

universe u

/-- At a residual router step, the residual coordinate is literally the
current chronological answer followed by the residual coordinate of the
answer-dependent continuation. -/
theorem residual_step_coordinate_eq
    {Output Slot : Type} [DecidableEq Slot]
    {slots : Finset Slot} {remaining : Nat}
    (next : Output → CausalSlotRouter Output Slot slots remaining)
    (tape : FreshAnswerTape Output (slots.card + (remaining + 1))) :
    ((CausalSlotRouter.residual next).coordinateEquiv tape).2 =
      let aligned := castFreshAnswerTape (by omega :
        slots.card + (remaining + 1) = (slots.card + remaining) + 1) tape
      (aligned.1, ((next aligned.1).coordinateEquiv aligned.2).2) := by
  rfl

/-- Equal residual coordinates at one residual router step have equal
literal current answers and equal recursively retained residual tapes. -/
theorem residual_step_coordinate_injective
    {Output Slot : Type} [DecidableEq Slot]
    {slots : Finset Slot} {remaining : Nat}
    (next : Output → CausalSlotRouter Output Slot slots remaining)
    (left right : FreshAnswerTape Output (slots.card + (remaining + 1)))
    (equal : ((CausalSlotRouter.residual next).coordinateEquiv left).2 =
      ((CausalSlotRouter.residual next).coordinateEquiv right).2) :
    let leftAligned := castFreshAnswerTape (by omega :
      slots.card + (remaining + 1) = (slots.card + remaining) + 1) left
    let rightAligned := castFreshAnswerTape (by omega :
      slots.card + (remaining + 1) = (slots.card + remaining) + 1) right
    leftAligned.1 = rightAligned.1 ∧
      ((next leftAligned.1).coordinateEquiv leftAligned.2).2 =
        ((next rightAligned.1).coordinateEquiv rightAligned.2).2 := by
  rw [residual_step_coordinate_eq, residual_step_coordinate_eq] at equal
  exact Prod.ext_iff.mp equal

/-- If a concrete pre-answer trace takes only residual destinations, equality
of the compiled residual coordinate forces the same literal chronological
prefix on a second tape.  The continuation state is allowed to depend on
earlier answers: the induction first recovers that answer, then follows the
same deterministic continuation.

This is deliberately a source-neutral fact.  The Tag-73 bridge need only
show that the returned-prover segment precedes the selected final-work/q16
anchor, so its labels are all `none`. -/
theorem all_residual_trace_forces_right_prefix
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    {machine : PreAnswerSlotMachine Output Slot State}
    {slots : Finset Slot} {residual : Nat}
    {initial finalState : State}
    {steps : List (Option Slot × Output)}
    (trace : MachineLabeledTrace machine initial steps finalState)
    (allResidual : namedTraceSlots steps = [])
    (residualEnough : residualTraceSteps steps ≤ residual)
    (left right : FreshAnswerTape Output (slots.card + residual))
    (leftExact : freshAnswerTapeToList left =
      steps.map Prod.snd ++
        (freshAnswerTapeToList left).drop steps.length)
    (coordinateExact :
      ((machine.router slots residual initial).coordinateEquiv left).2 =
        ((machine.router slots residual initial).coordinateEquiv right).2) :
    ∃ rightRemaining,
      freshAnswerTapeToList right = steps.map Prod.snd ++ rightRemaining := by
  induction trace generalizing slots residual left right with
  | nil state =>
      exact ⟨freshAnswerTapeToList right, by simp⟩
  | @cons state finalState label answer tail preferred rest ih =>
      cases label with
      | some slot =>
          simp [namedTraceSlots] at allResidual
      | none =>
          have residualPositive : 0 < residual := by
            simp only [residualTraceSteps] at residualEnough
            omega
          cases residual with
          | zero => omega
          | succ priorResidual =>
              have choice : chooseRemainingDestination slots
                  (priorResidual + 1)
                  (by omega : 0 < slots.card + (priorResidual + 1))
                  (machine.preferredSlot state) =
                .residual (by omega) := by
                simp [preferred, chooseRemainingDestination]
              have routerExact : machine.router slots (priorResidual + 1)
                  state = CausalSlotRouter.residual (fun current =>
                    machine.router slots priorResidual
                      (machine.afterAnswer state current)) := by
                exact router_eq_residual_of_choice machine slots priorResidual
                  state (by omega) choice
              have coordinateExact' :
                  ((CausalSlotRouter.residual (fun current =>
                    machine.router slots priorResidual
                      (machine.afterAnswer state current))).coordinateEquiv
                      left).2 =
                    ((CausalSlotRouter.residual (fun current =>
                      machine.router slots priorResidual
                        (machine.afterAnswer state current))).coordinateEquiv
                      right).2 := by
                simpa only [routerExact] using coordinateExact
              obtain ⟨headExact, tailCoordinateExact⟩ :=
                residual_step_coordinate_injective
                  (next := fun current => machine.router slots priorResidual
                    (machine.afterAnswer state current)) left right
                  coordinateExact'
              let leftAligned := castFreshAnswerTape
                (residualStepLengthEq slots.card priorResidual) left
              let rightAligned := castFreshAnswerTape
                (residualStepLengthEq slots.card priorResidual) right
              have leftHeadExact : leftAligned.1 = answer := by
                have leftList : freshAnswerTapeToList leftAligned =
                    answer ::
                      (tail.map Prod.snd ++
                        (freshAnswerTapeToList left).drop tail.length.succ) := by
                  unfold leftAligned
                  rw [fresh_answer_tape_to_list_cast]
                  simpa only [List.map_cons, Prod.snd, List.cons_append,
                    List.length_cons, List.drop_succ_cons] using leftExact
                exact List.cons.inj (by
                  simpa only [freshAnswerTapeToList] using leftList) |>.1
              have headExact' : rightAligned.1 = answer := by
                calc
                  rightAligned.1 = leftAligned.1 := by
                    simpa only [leftAligned, rightAligned] using headExact.symm
                  _ = answer := leftHeadExact
              have tailCoordinateExact'' :
                  ((machine.router slots priorResidual
                    (machine.afterAnswer state leftAligned.1)).coordinateEquiv
                    leftAligned.2).2 =
                  ((machine.router slots priorResidual
                    (machine.afterAnswer state rightAligned.1)).coordinateEquiv
                    rightAligned.2).2 := by
                simpa only [leftAligned, rightAligned] using tailCoordinateExact
              have tailCoordinateExact' :
                  ((machine.router slots priorResidual
                    (machine.afterAnswer state answer)).coordinateEquiv
                    leftAligned.2).2 =
                  ((machine.router slots priorResidual
                    (machine.afterAnswer state answer)).coordinateEquiv
                    rightAligned.2).2 := by
                rw [leftHeadExact, headExact'] at tailCoordinateExact''
                exact tailCoordinateExact''
              have tailResidual : residualTraceSteps tail ≤ priorResidual := by
                simp only [residualTraceSteps] at residualEnough
                omega
              have tailAllResidual : namedTraceSlots tail = [] := by
                simpa [namedTraceSlots] using allResidual
              have leftTailExact : freshAnswerTapeToList leftAligned.2 =
                  tail.map Prod.snd ++
                    (freshAnswerTapeToList leftAligned.2).drop tail.length := by
                have leftList : freshAnswerTapeToList leftAligned =
                    answer ::
                      (tail.map Prod.snd ++
                        (freshAnswerTapeToList left).drop tail.length.succ) := by
                  unfold leftAligned
                  rw [fresh_answer_tape_to_list_cast]
                  simpa only [List.map_cons, Prod.snd, List.cons_append,
                    List.length_cons, List.drop_succ_cons] using leftExact
                have tailList : freshAnswerTapeToList leftAligned.2 =
                    tail.map Prod.snd ++
                      (freshAnswerTapeToList left).drop tail.length.succ := by
                  exact List.cons.inj (by
                    simpa only [freshAnswerTapeToList] using leftList) |>.2
                rw [tailList]
                rw [List.drop_append]
                simp [List.length_map]
              obtain ⟨rightRemaining, rightTailExact⟩ := ih tailAllResidual
                tailResidual leftAligned.2 rightAligned.2 leftTailExact
                tailCoordinateExact'
              refine ⟨rightRemaining, ?_⟩
              have rightList : freshAnswerTapeToList rightAligned =
                  answer :: (tail.map Prod.snd ++ rightRemaining) := by
                simpa only [headExact', freshAnswerTapeToList] using
                  congrArg (fun tail => answer :: tail) rightTailExact
              unfold rightAligned at rightList
              rw [fresh_answer_tape_to_list_cast] at rightList
              simpa only [List.map_cons, Prod.snd, List.cons_append] using
                rightList

#print axioms residual_step_coordinate_eq
#print axioms residual_step_coordinate_injective
#print axioms all_residual_trace_forces_right_prefix

end

end AspisK1.V7Tag73CausalResidualCoordinatePrefix
