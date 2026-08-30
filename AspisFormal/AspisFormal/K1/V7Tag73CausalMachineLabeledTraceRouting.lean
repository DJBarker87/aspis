import AspisFormal.K1.V7Tag73CausalMachinePrefixRouting
import AspisFormal.K1.V7Tag73ExactCausalRouterTapeAlignment

/-!
# Routing a finite pre-answer-labelled trace

This module supplies the generic deterministic bridge between a causal slot
machine and its compiled router.  A labelled trace records the machine's
choice before each chronological answer.  If named labels are distinct and
the residual component covers every unlabelled exposure, replaying the trace
through the compiled router consumes exactly those destinations.  In
particular, every named answer is recovered by `causalRoutedAnswer?`.

The result is independent of Tag-73 grammar.  The source layer only has to
prove that the concrete final-work/q16 controller emits the intended labels
on the literal accepted trace and instantiate the already-proved residual
capacity inequality.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalMachineLabeledTraceRouting

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalMachinePrefixRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73OperationalOracleExposure

noncomputable section

universe u

/-- A finite chronological execution whose label is fixed before its answer
is supplied. -/
inductive MachineLabeledTrace
    {Output Slot : Type} {State : Type u}
    (machine : PreAnswerSlotMachine Output Slot State) :
    State → List (Option Slot × Output) → State → Prop where
  | nil (state : State) : MachineLabeledTrace machine state [] state
  | cons {state finalState : State} {label : Option Slot} {answer : Output}
      {tail : List (Option Slot × Output)}
      (preferred : machine.preferredSlot state = label)
      (rest : MachineLabeledTrace machine
        (machine.afterAnswer state answer) tail finalState) :
      MachineLabeledTrace machine state ((label, answer) :: tail) finalState

/-- Named destinations, in chronological order. -/
def namedTraceSlots {Output Slot : Type} :
    List (Option Slot × Output) → List Slot
  | [] => []
  | (none, _answer) :: tail => namedTraceSlots tail
  | (some slot, _answer) :: tail => slot :: namedTraceSlots tail

/-- Number of chronological answers deliberately left in the residual tape. -/
def residualTraceSteps {Output Slot : Type} :
    List (Option Slot × Output) → Nat
  | [] => 0
  | (none, _answer) :: tail => residualTraceSteps tail + 1
  | (some _slot, _answer) :: tail => residualTraceSteps tail

@[simp] theorem named_trace_slots_nil {Output Slot : Type} :
    namedTraceSlots ([] : List (Option Slot × Output)) = [] := by
  rfl

@[simp] theorem named_trace_slots_none_cons
    {Output Slot : Type} (answer : Output)
    (tail : List (Option Slot × Output)) :
    namedTraceSlots ((none, answer) :: tail) = namedTraceSlots tail := by
  rfl

@[simp] theorem named_trace_slots_some_cons
    {Output Slot : Type} (slot : Slot) (answer : Output)
    (tail : List (Option Slot × Output)) :
    namedTraceSlots ((some slot, answer) :: tail) =
      slot :: namedTraceSlots tail := by
  rfl

@[simp] theorem residual_trace_steps_nil {Output Slot : Type} :
    residualTraceSteps ([] : List (Option Slot × Output)) = 0 := by
  rfl

@[simp] theorem residual_trace_steps_none_cons
    {Output Slot : Type} (answer : Output)
    (tail : List (Option Slot × Output)) :
    residualTraceSteps ((none, answer) :: tail) =
      residualTraceSteps tail + 1 := by
  rfl

@[simp] theorem residual_trace_steps_some_cons
    {Output Slot : Type} (slot : Slot) (answer : Output)
    (tail : List (Option Slot × Output)) :
    residualTraceSteps ((some slot, answer) :: tail) =
      residualTraceSteps tail := by
  rfl

theorem named_trace_slots_append
    {Output Slot : Type} :
    ∀ first second : List (Option Slot × Output),
      namedTraceSlots (first ++ second) =
        namedTraceSlots first ++ namedTraceSlots second := by
  intro first
  induction first with
  | nil => intro second; simp
  | cons head tail ih =>
      intro second
      rcases head with ⟨label, answer⟩
      cases label <;> simp [namedTraceSlots, ih]

theorem residual_trace_steps_append
    {Output Slot : Type} :
    ∀ first second : List (Option Slot × Output),
      residualTraceSteps (first ++ second) =
        residualTraceSteps first + residualTraceSteps second := by
  intro first
  induction first with
  | nil => intro second; simp [residualTraceSteps]
  | cons head tail ih =>
      intro second
      rcases head with ⟨label, answer⟩
      cases label <;> simp [residualTraceSteps, ih, Nat.add_assoc,
        Nat.add_comm]

/-- Split a labelled execution at any list decomposition. -/
theorem machine_labeled_trace_append_split
    {Output Slot : Type} {State : Type u}
    {machine : PreAnswerSlotMachine Output Slot State}
    {initial finalState : State}
    (first second : List (Option Slot × Output))
    (trace : MachineLabeledTrace machine initial (first ++ second)
      finalState) :
    ∃ middleState,
      MachineLabeledTrace machine initial first middleState ∧
      MachineLabeledTrace machine middleState second finalState := by
  induction first generalizing initial with
  | nil =>
      exact ⟨initial, .nil initial, trace⟩
  | cons head tail ih =>
      rcases head with ⟨label, answer⟩
      cases trace with
      | cons preferred rest =>
          obtain ⟨middleState, prefixPart, suffix⟩ := ih rest
          exact ⟨middleState, .cons preferred prefixPart, suffix⟩

/-- A labelled prefix consumes exactly its distinct named destinations and
one residual destination for every unlabelled step. -/
theorem machine_labeled_trace_constructs_router_prefix
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    {machine : PreAnswerSlotMachine Output Slot State}
    {slots : Finset Slot} {residual : Nat}
    {initial finalState : State}
    {steps : List (Option Slot × Output)}
    (trace : MachineLabeledTrace machine initial steps finalState)
    (namedNodup : (namedTraceSlots steps).Nodup)
    (namedMember : ∀ slot ∈ namedTraceSlots steps, slot ∈ slots)
    (residualEnough : residualTraceSteps steps ≤ residual)
    (tape : FreshAnswerTape Output (slots.card + residual))
    (remainingValues : List Output)
    (tapeExact : freshAnswerTapeToList tape =
      steps.map Prod.snd ++ remainingValues) :
    ∃ remainingTape : FreshAnswerTape Output
        ((slots \ (namedTraceSlots steps).toFinset).card +
          (residual - residualTraceSteps steps)),
      MachineRouterPrefix machine
        (slots := slots) (residual := residual) initial tape
        (remainingSlots := slots \ (namedTraceSlots steps).toFinset)
        (remainingResidual := residual - residualTraceSteps steps)
        finalState remainingTape ∧
      freshAnswerTapeToList remainingTape = remainingValues := by
  induction trace generalizing slots residual tape remainingValues with
  | nil state =>
      have result : ∃ remainingTape : FreshAnswerTape Output
          (slots.card + residual),
          MachineRouterPrefix machine
            (slots := slots) (residual := residual) state tape
            (remainingSlots := slots) (remainingResidual := residual)
            state remainingTape ∧
          freshAnswerTapeToList remainingTape = remainingValues :=
        ⟨tape, .refl slots residual state tape, by simpa using tapeExact⟩
      have emptyDiff : slots \ (namedTraceSlots
          ([] : List (Option Slot × Output))).toFinset = slots := by
        ext slot
        simp [namedTraceSlots]
      rw [emptyDiff]
      simpa [residualTraceSteps] using result
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
              let alignedTape := castFreshAnswerTape
                (residualStepLengthEq slots.card priorResidual) tape
              have alignedListRaw : freshAnswerTapeToList alignedTape =
                  answer :: (tail.map Prod.snd ++ remainingValues) := by
                unfold alignedTape
                rw [fresh_answer_tape_to_list_cast]
                simpa only [List.map_cons, Prod.snd, List.cons_append] using
                  tapeExact
              rcases alignedExact : alignedTape with
                ⟨headAnswer, tailTape⟩
              have alignedList :
                  headAnswer :: freshAnswerTapeToList tailTape =
                    answer :: (tail.map Prod.snd ++ remainingValues) := by
                simpa only [alignedExact, freshAnswerTapeToList] using
                  alignedListRaw
              have headExact : headAnswer = answer :=
                List.cons.inj alignedList |>.1
              subst headAnswer
              have tailExact : freshAnswerTapeToList tailTape =
                  tail.map Prod.snd ++ remainingValues :=
                List.cons.inj alignedList |>.2
              have tailNodup : (namedTraceSlots tail).Nodup := by
                simpa [namedTraceSlots] using namedNodup
              have tailMember : ∀ slot ∈ namedTraceSlots tail,
                  slot ∈ slots := by
                intro slot member
                exact namedMember slot (by simpa [namedTraceSlots] using member)
              have tailResidual : residualTraceSteps tail ≤ priorResidual := by
                simp only [residualTraceSteps] at residualEnough
                omega
              obtain ⟨remainingTape, route, remainingExact⟩ :=
                ih tailNodup tailMember tailResidual tailTape remainingValues
                  tailExact
              have route' : MachineRouterPrefix machine state tape finalState
                  remainingTape := by
                apply MachineRouterPrefix.residual (by omega) choice tape
                  answer tailTape
                · change alignedTape = (answer, tailTape)
                  simpa using alignedExact
                · exact route
              have result : ∃ remainingTape : FreshAnswerTape Output
                  ((slots \ (namedTraceSlots tail).toFinset).card +
                    (priorResidual - residualTraceSteps tail)),
                  MachineRouterPrefix machine
                    (slots := slots) (residual := priorResidual + 1)
                    state tape
                    (remainingSlots :=
                      slots \ (namedTraceSlots tail).toFinset)
                    (remainingResidual :=
                      priorResidual - residualTraceSteps tail)
                    finalState remainingTape ∧
                  freshAnswerTapeToList remainingTape = remainingValues :=
                ⟨remainingTape, route', remainingExact⟩
              have residualExact :
                  priorResidual + 1 - (residualTraceSteps tail + 1) =
                    priorResidual - residualTraceSteps tail := by
                omega
              change ∃ remainingTape : FreshAnswerTape Output
                  ((slots \ (namedTraceSlots tail).toFinset).card +
                    (priorResidual + 1 -
                      (residualTraceSteps tail + 1))),
                  MachineRouterPrefix machine
                    (slots := slots) (residual := priorResidual + 1)
                    state tape
                    (remainingSlots :=
                      slots \ (namedTraceSlots tail).toFinset)
                    (remainingResidual := priorResidual + 1 -
                      (residualTraceSteps tail + 1))
                    finalState remainingTape ∧
                  freshAnswerTapeToList remainingTape = remainingValues
              rw [residualExact]
              exact result
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
          let alignedTape := castFreshAnswerTape
            (specialStepLengthEq slots residual chosen) tape
          have alignedListRaw : freshAnswerTapeToList alignedTape =
              answer :: (tail.map Prod.snd ++ remainingValues) := by
            unfold alignedTape
            rw [fresh_answer_tape_to_list_cast]
            simpa only [List.map_cons, Prod.snd, List.cons_append] using
              tapeExact
          rcases alignedExact : alignedTape with ⟨headAnswer, tailTape⟩
          have alignedList :
              headAnswer :: freshAnswerTapeToList tailTape =
                answer :: (tail.map Prod.snd ++ remainingValues) := by
            simpa only [alignedExact, freshAnswerTapeToList] using
              alignedListRaw
          have headExact : headAnswer = answer :=
            List.cons.inj alignedList |>.1
          subst headAnswer
          have tailExact : freshAnswerTapeToList tailTape =
              tail.map Prod.snd ++ remainingValues :=
            List.cons.inj alignedList |>.2
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
          obtain ⟨remainingTape, route, remainingExact⟩ :=
            ih tailNodup tailMember residualEnough tailTape remainingValues
              tailExact
          have remainingSlotsExact :
              slots \ (slot :: namedTraceSlots tail).toFinset =
                slots.erase slot \ (namedTraceSlots tail).toFinset := by
            ext target
            simp [and_assoc, and_left_comm]
          have route' : MachineRouterPrefix machine state tape finalState
              remainingTape := by
            apply MachineRouterPrefix.special remainingPositive chosen choice
              tape answer tailTape
            · change alignedTape = (answer, tailTape)
              simpa using alignedExact
            · exact route
          have result : ∃ remainingTape : FreshAnswerTape Output
              ((slots.erase slot \ (namedTraceSlots tail).toFinset).card +
                (residual - residualTraceSteps tail)),
              MachineRouterPrefix machine
                (slots := slots) (residual := residual) state tape
                (remainingSlots :=
                  slots.erase slot \ (namedTraceSlots tail).toFinset)
                (remainingResidual := residual - residualTraceSteps tail)
                finalState remainingTape ∧
              freshAnswerTapeToList remainingTape = remainingValues :=
            ⟨remainingTape, route', remainingExact⟩
          change ∃ remainingTape : FreshAnswerTape Output
              ((slots \ (slot :: namedTraceSlots tail).toFinset).card +
                (residual - residualTraceSteps tail)),
              MachineRouterPrefix machine
                (slots := slots) (residual := residual) state tape
                (remainingSlots :=
                  slots \ (slot :: namedTraceSlots tail).toFinset)
                (remainingResidual := residual - residualTraceSteps tail)
                finalState remainingTape ∧
              freshAnswerTapeToList remainingTape = remainingValues
          rw [remainingSlotsExact]
          exact result

/-- Every named step of a valid labelled trace receives its literal
chronological answer in the compiled router. -/
theorem machine_labeled_trace_routes_named_answer
    {Output Slot : Type} {State : Type u} [DecidableEq Slot]
    {machine : PreAnswerSlotMachine Output Slot State}
    {slots : Finset Slot} {residual : Nat}
    {initial finalState : State}
    {steps : List (Option Slot × Output)}
    (trace : MachineLabeledTrace machine initial steps finalState)
    (namedNodup : (namedTraceSlots steps).Nodup)
    (namedMember : ∀ slot ∈ namedTraceSlots steps, slot ∈ slots)
    (residualEnough : residualTraceSteps steps ≤ residual)
    (tape : FreshAnswerTape Output (slots.card + residual))
    (remainingValues : List Output)
    (tapeExact : freshAnswerTapeToList tape =
      steps.map Prod.snd ++ remainingValues)
    (prior later : List (Option Slot × Output))
    (target : Slot) (answer : Output)
    (decomposition : steps = prior ++ (some target, answer) :: later) :
    causalRoutedAnswer? target (machine.router slots residual initial) tape =
      some answer := by
  have namedDecomposition : namedTraceSlots steps =
      namedTraceSlots prior ++ target :: namedTraceSlots later := by
    rw [decomposition, named_trace_slots_append]
    simp [namedTraceSlots]
  have priorNodup : (namedTraceSlots prior).Nodup := by
    rw [namedDecomposition] at namedNodup
    exact (List.nodup_append.mp namedNodup).1
  have targetNotPrior : target ∉ namedTraceSlots prior := by
    rw [namedDecomposition] at namedNodup
    have separated := (List.nodup_append.mp namedNodup).2.2
    intro member
    exact separated target member target (by simp) rfl
  have priorMember : ∀ slot ∈ namedTraceSlots prior, slot ∈ slots := by
    intro slot member
    exact namedMember slot (by rw [namedDecomposition]; simp [member])
  have targetMember : target ∈ slots := by
    exact namedMember target (by rw [namedDecomposition]; simp)
  have priorResidual : residualTraceSteps prior ≤ residual := by
    have countDecomposition : residualTraceSteps steps =
        residualTraceSteps prior + residualTraceSteps later := by
      rw [decomposition, residual_trace_steps_append]
      simp [residualTraceSteps]
    omega
  obtain ⟨reached, prefixTrace, selectedTrace⟩ :=
    machine_labeled_trace_append_split prior
      ((some target, answer) :: later) (by
        simpa [decomposition] using trace)
  cases selectedTrace with
  | cons selectedPreferred selectedRest =>
      have prefixTapeExact : freshAnswerTapeToList tape =
          prior.map Prod.snd ++
            (answer :: (later.map Prod.snd ++ remainingValues)) := by
        rw [tapeExact, decomposition]
        simp [List.map_append, List.append_assoc]
      obtain ⟨remainingTape, route, remainingExact⟩ :=
        machine_labeled_trace_constructs_router_prefix prefixTrace priorNodup
          priorMember priorResidual tape
          (answer :: (later.map Prod.snd ++ remainingValues)) prefixTapeExact
      let remainingSlots := slots \ (namedTraceSlots prior).toFinset
      let remainingResidual := residual - residualTraceSteps prior
      have remainingMember : target ∈ remainingSlots := by
        simp [remainingSlots, targetMember, targetNotPrior]
      let chosen : ↥remainingSlots := ⟨target, remainingMember⟩
      let alignedTape := castFreshAnswerTape
        (specialStepLengthEq remainingSlots remainingResidual chosen)
        remainingTape
      have alignedListRaw : freshAnswerTapeToList alignedTape =
          answer :: (later.map Prod.snd ++ remainingValues) := by
        unfold alignedTape
        rw [fresh_answer_tape_to_list_cast, remainingExact]
      rcases alignedExact : alignedTape with ⟨headAnswer, tailTape⟩
      have alignedList :
          headAnswer :: freshAnswerTapeToList tailTape =
            answer :: (later.map Prod.snd ++ remainingValues) := by
        simpa only [alignedExact, freshAnswerTapeToList] using alignedListRaw
      have headExact : headAnswer = answer :=
        List.cons.inj alignedList |>.1
      subst headAnswer
      apply machine_router_prefix_then_preferred_routed_answer route target
        remainingMember selectedPreferred answer tailTape
      change alignedTape = (answer, tailTape)
      simpa using alignedExact

#print axioms MachineLabeledTrace
#print axioms namedTraceSlots
#print axioms residualTraceSteps
#print axioms named_trace_slots_append
#print axioms residual_trace_steps_append
#print axioms machine_labeled_trace_append_split
#print axioms machine_labeled_trace_constructs_router_prefix
#print axioms machine_labeled_trace_routes_named_answer

end

end AspisK1.V7Tag73CausalMachineLabeledTraceRouting
