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
open AspisK1.V7Tag73CausalSlotRouterRealization
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

/-- At a named router step, equality of the selected named coordinate fixes
the literal current answer.  No equality is required for any other named
coordinate. -/
theorem special_step_selected_coordinate_injective
    {Output Slot : Type} [DecidableEq Slot]
    {slots : Finset Slot} {residual : Nat}
    (chosen : ↥slots)
    (next : Output → CausalSlotRouter Output Slot
      (slots.erase chosen.1) residual)
    (left right : FreshAnswerTape Output (slots.card + residual))
    (equal :
      ((CausalSlotRouter.special chosen next).coordinateEquiv left).1 chosen =
        ((CausalSlotRouter.special chosen next).coordinateEquiv right).1
          chosen) :
    let leftAligned := castFreshAnswerTape
      (specialStepLengthEq slots residual chosen) left
    let rightAligned := castFreshAnswerTape
      (specialStepLengthEq slots residual chosen) right
    leftAligned.1 = rightAligned.1 := by
  rw [special_slot_receives_current_answer,
    special_slot_receives_current_answer] at equal
  exact equal

/-- A named step leaves the residual coordinate equal to the residual
coordinate of its answer-dependent continuation. -/
theorem special_step_residual_coordinate_eq
    {Output Slot : Type} [DecidableEq Slot]
    {slots : Finset Slot} {residual : Nat}
    (chosen : ↥slots)
    (next : Output → CausalSlotRouter Output Slot
      (slots.erase chosen.1) residual)
    (tape : FreshAnswerTape Output (slots.card + residual)) :
    ((CausalSlotRouter.special chosen next).coordinateEquiv tape).2 =
      let aligned := castFreshAnswerTape
        (specialStepLengthEq slots residual chosen) tape
      ((next aligned.1).coordinateEquiv aligned.2).2 := by
  rfl

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

/-- Equality of the residual coordinate together with equality at precisely
the named slots used by a concrete trace forces the same literal prefix.
Coordinates reserved for later named steps may still differ.  This is the
mixed named/residual form needed by the work-dependent q16 factorisation. -/
theorem trace_forces_right_prefix_of_used_coordinate_agreement
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    {machine : PreAnswerSlotMachine Output Slot State}
    {slots : Finset Slot} {residual : Nat}
    {initial finalState : State}
    {steps : List (Option Slot × Output)}
    (trace : MachineLabeledTrace machine initial steps finalState)
    (namedNodup : (namedTraceSlots steps).Nodup)
    (namedMember : ∀ slot ∈ namedTraceSlots steps, slot ∈ slots)
    (residualEnough : residualTraceSteps steps ≤ residual)
    (left right : FreshAnswerTape Output (slots.card + residual))
    (leftExact : freshAnswerTapeToList left =
      steps.map Prod.snd ++
        (freshAnswerTapeToList left).drop steps.length)
    (residualExact :
      ((machine.router slots residual initial).coordinateEquiv left).2 =
        ((machine.router slots residual initial).coordinateEquiv right).2)
    (namedExact : ∀ current : ↥slots,
      current.1 ∈ namedTraceSlots steps →
        ((machine.router slots residual initial).coordinateEquiv left).1
            current =
          ((machine.router slots residual initial).coordinateEquiv right).1
            current) :
    ∃ rightRemaining,
      freshAnswerTapeToList right = steps.map Prod.snd ++ rightRemaining := by
  induction trace generalizing slots residual left right with
  | nil state =>
      exact ⟨freshAnswerTapeToList right, by simp⟩
  | @cons state finalState label answer tail preferred rest ih =>
      cases label with
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
              have residualExact' :
                  ((CausalSlotRouter.residual (fun current =>
                    machine.router slots priorResidual
                      (machine.afterAnswer state current))).coordinateEquiv
                      left).2 =
                    ((CausalSlotRouter.residual (fun current =>
                      machine.router slots priorResidual
                        (machine.afterAnswer state current))).coordinateEquiv
                      right).2 := by
                simpa only [routerExact] using residualExact
              obtain ⟨headExact, tailResidualExact⟩ :=
                residual_step_coordinate_injective
                  (next := fun current => machine.router slots priorResidual
                    (machine.afterAnswer state current)) left right
                  residualExact'
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
              have rightHeadExact : rightAligned.1 = answer := by
                calc
                  rightAligned.1 = leftAligned.1 := by
                    simpa only [leftAligned, rightAligned] using headExact.symm
                  _ = answer := leftHeadExact
              have tailResidualExact' :
                  ((machine.router slots priorResidual
                    (machine.afterAnswer state answer)).coordinateEquiv
                      leftAligned.2).2 =
                  ((machine.router slots priorResidual
                    (machine.afterAnswer state answer)).coordinateEquiv
                      rightAligned.2).2 := by
                simpa only [leftAligned, rightAligned, leftHeadExact,
                  rightHeadExact] using tailResidualExact
              have tailNamedExact : ∀ current : ↥slots,
                  current.1 ∈ namedTraceSlots tail →
                    ((machine.router slots priorResidual
                      (machine.afterAnswer state answer)).coordinateEquiv
                        leftAligned.2).1 current =
                    ((machine.router slots priorResidual
                      (machine.afterAnswer state answer)).coordinateEquiv
                        rightAligned.2).1 current := by
                intro current member
                have topExact := namedExact current (by
                  simpa [namedTraceSlots] using member)
                rw [routerExact,
                  residual_step_named_slot_receives_tail_answer,
                  residual_step_named_slot_receives_tail_answer] at topExact
                simpa only [leftAligned, rightAligned, leftHeadExact,
                  rightHeadExact] using topExact
              have tailResidualEnough :
                  residualTraceSteps tail ≤ priorResidual := by
                simp only [residualTraceSteps] at residualEnough
                omega
              have tailNodup : (namedTraceSlots tail).Nodup := by
                simpa [namedTraceSlots] using namedNodup
              have tailMember : ∀ slot ∈ namedTraceSlots tail,
                  slot ∈ slots := by
                intro slot member
                exact namedMember slot (by
                  simpa [namedTraceSlots] using member)
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
                rw [tailList, List.drop_append]
                simp [List.length_map]
              obtain ⟨rightRemaining, rightTailExact⟩ :=
                ih tailNodup tailMember tailResidualEnough leftAligned.2
                  rightAligned.2 leftTailExact tailResidualExact'
                  tailNamedExact
              refine ⟨rightRemaining, ?_⟩
              have rightList : freshAnswerTapeToList rightAligned =
                  answer :: (tail.map Prod.snd ++ rightRemaining) := by
                simpa only [rightHeadExact, freshAnswerTapeToList] using
                  congrArg (fun values => answer :: values) rightTailExact
              unfold rightAligned at rightList
              rw [fresh_answer_tape_to_list_cast] at rightList
              simpa only [List.map_cons, Prod.snd, List.cons_append] using
                rightList
      | some slot =>
          have slotMember : slot ∈ slots :=
            namedMember slot (by simp [namedTraceSlots])
          have remainingPositive : 0 < slots.card + residual := by
            have slotsPositive : 0 < slots.card := Finset.card_pos.mpr
              ⟨slot, slotMember⟩
            omega
          let chosen : ↥slots := ⟨slot, slotMember⟩
          have choice : chooseRemainingDestination slots residual
              remainingPositive (machine.preferredSlot state) =
            .special chosen := by
            simp [preferred, chooseRemainingDestination, chosen, slotMember]
          have routerExact : machine.router slots residual state =
              CausalSlotRouter.special chosen (fun current =>
                machine.router (slots.erase slot) residual
                  (machine.afterAnswer state current)) := by
            exact router_eq_special_of_choice machine slots residual state
              remainingPositive chosen choice
          have selectedExact :
              ((CausalSlotRouter.special chosen (fun current =>
                machine.router (slots.erase slot) residual
                  (machine.afterAnswer state current))).coordinateEquiv
                    left).1 chosen =
              ((CausalSlotRouter.special chosen (fun current =>
                machine.router (slots.erase slot) residual
                  (machine.afterAnswer state current))).coordinateEquiv
                    right).1 chosen := by
            simpa only [routerExact] using namedExact chosen (by
              simp [chosen, namedTraceSlots])
          have headExact := special_step_selected_coordinate_injective chosen
            (fun current => machine.router (slots.erase slot) residual
              (machine.afterAnswer state current)) left right selectedExact
          let leftAligned := castFreshAnswerTape
            (specialStepLengthEq slots residual chosen) left
          let rightAligned := castFreshAnswerTape
            (specialStepLengthEq slots residual chosen) right
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
          have rightHeadExact : rightAligned.1 = answer := by
            calc
              rightAligned.1 = leftAligned.1 := by
                simpa only [leftAligned, rightAligned] using headExact.symm
              _ = answer := leftHeadExact
          have tailResidualExact :
              ((machine.router (slots.erase slot) residual
                (machine.afterAnswer state answer)).coordinateEquiv
                  leftAligned.2).2 =
              ((machine.router (slots.erase slot) residual
                (machine.afterAnswer state answer)).coordinateEquiv
                  rightAligned.2).2 := by
            rw [routerExact, special_step_residual_coordinate_eq,
              special_step_residual_coordinate_eq] at residualExact
            simpa only [leftAligned, rightAligned, leftHeadExact,
              rightHeadExact] using residualExact
          have slotAbsent : slot ∉ namedTraceSlots tail := by
            exact (List.nodup_cons.mp (by
              simpa [namedTraceSlots] using namedNodup)).1
          have tailNodup : (namedTraceSlots tail).Nodup := by
            exact (List.nodup_cons.mp (by
              simpa [namedTraceSlots] using namedNodup)).2
          have tailMember : ∀ target ∈ namedTraceSlots tail,
              target ∈ slots.erase slot := by
            intro target member
            exact Finset.mem_erase.mpr ⟨fun equal =>
              slotAbsent (equal.symm ▸ member),
              namedMember target (by simp [namedTraceSlots, member])⟩
          have tailNamedExact : ∀ current : ↥(slots.erase slot),
              current.1 ∈ namedTraceSlots tail →
                ((machine.router (slots.erase slot) residual
                  (machine.afterAnswer state answer)).coordinateEquiv
                    leftAligned.2).1 current =
                ((machine.router (slots.erase slot) residual
                  (machine.afterAnswer state answer)).coordinateEquiv
                    rightAligned.2).1 current := by
            intro current member
            let parent : ↥slots :=
              ⟨current.1, Finset.mem_of_mem_erase current.2⟩
            have different : parent.1 ≠ chosen.1 := by
              simpa [parent, chosen] using (Finset.mem_erase.mp current.2).1
            have topExact := namedExact parent (by
              simp [parent, namedTraceSlots, member])
            rw [routerExact,
              special_other_slot_receives_tail_answer chosen parent different,
              special_other_slot_receives_tail_answer chosen parent different]
              at topExact
            simpa only [leftAligned, rightAligned, leftHeadExact,
              rightHeadExact, parent, chosen] using topExact
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
            rw [tailList, List.drop_append]
            simp [List.length_map]
          obtain ⟨rightRemaining, rightTailExact⟩ :=
            ih tailNodup tailMember residualEnough leftAligned.2
              rightAligned.2 leftTailExact tailResidualExact tailNamedExact
          refine ⟨rightRemaining, ?_⟩
          have rightList : freshAnswerTapeToList rightAligned =
              answer :: (tail.map Prod.snd ++ rightRemaining) := by
            simpa only [rightHeadExact, freshAnswerTapeToList] using
              congrArg (fun values => answer :: values) rightTailExact
          unfold rightAligned at rightList
          rw [fresh_answer_tape_to_list_cast] at rightList
          simpa only [List.map_cons, Prod.snd, List.cons_append] using
            rightList

#print axioms residual_step_coordinate_eq
#print axioms residual_step_coordinate_injective
#print axioms special_step_selected_coordinate_injective
#print axioms special_step_residual_coordinate_eq
#print axioms all_residual_trace_forces_right_prefix
#print axioms trace_forces_right_prefix_of_used_coordinate_agreement

end

end AspisK1.V7Tag73CausalResidualCoordinatePrefix
