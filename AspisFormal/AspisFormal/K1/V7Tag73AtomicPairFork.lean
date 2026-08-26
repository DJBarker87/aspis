import AspisFormal.K1.V7Tag73ExecutableHistoryMatcher

/-!
# Atomic output/advance forks for generated Tag-73 squeezes

Every generated replay point targets one complete `squeezePair` action.  Its
two SHA calls are the output and advance domains of the same pre-action
transcript state.  This module also computes the first frozen-Q1 occurrence
of either input and proves the usual first-occurrence facts directly from the
list recursion.

The two call positions do not create two verifier restoration states: choosing
either half maps to the same concrete complete, previously seen, nonempty and
binding-preserving snapshot.  No prediction or probability statement is made.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73AtomicPairFork

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73DagActionAlignment
open AspisK1.V7Tag73ConcreteStateRestoration
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7FsAokExperiment

/-! ## The exact atomic pair -/

noncomputable def generatedPairState
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) : Digest256 :=
  (concreteRestoration execution generated).snapshot.core.digest

noncomputable def generatedPairInput
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) : SqueezeHalf → ShaInput
  | .output => bytes (generatedPairState execution generated) ++ [domSqueeze]
  | .advance => bytes (generatedPairState execution generated) ++ [domAdvance]

noncomputable def generatedPairInputs
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) : List ShaInput :=
  [generatedPairInput execution generated .output,
   generatedPairInput execution generated .advance]

@[simp] theorem generated_pair_output_input_exact
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    generatedPairInput execution generated .output =
      bytes (generatedPairState execution generated) ++ [domSqueeze] := by
  rfl

@[simp] theorem generated_pair_advance_input_exact
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    generatedPairInput execution generated .advance =
      bytes (generatedPairState execution generated) ++ [domAdvance] := by
  rfl

theorem generated_pair_is_exact_next_action_input_list
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    let restoration := concreteRestoration execution generated
    generatedPairInputs execution generated =
      actionInputs restoration.snapshot.bindings restoration.snapshot.core
        (.squeezePair restoration.checkpoint.owner
          restoration.checkpoint.block) := by
  have exactInputs :=
    (restoration_squeeze_is_one_atomic_two_query_action
      (concreteRestoration execution generated)).2.1
  exact exactInputs.symm

theorem generated_pair_uses_one_pre_action_state
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    ∃ state : Digest256,
      state = (concreteRestoration execution generated).snapshot.core.digest ∧
      generatedPairInput execution generated .output =
        bytes state ++ [domSqueeze] ∧
      generatedPairInput execution generated .advance =
        bytes state ++ [domAdvance] := by
  exact ⟨generatedPairState execution generated, rfl, rfl, rfl⟩

theorem generated_pair_inputs_are_distinct
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    generatedPairInput execution generated .output ≠
      generatedPairInput execution generated .advance := by
  exact squeeze_output_and_advance_inputs_are_distinct
    (generatedPairState execution generated)

/-! ## Executable first occurrence among the two inputs -/

structure PairOccurrenceSplit where
  before : List QueryRecord
  chosen : QueryRecord
  after : List QueryRecord

def firstEitherInputOccurrence (outputInput advanceInput : ShaInput) :
    List QueryRecord → Option PairOccurrenceSplit
  | [] => none
  | record :: rest =>
      if record.input = outputInput ∨ record.input = advanceInput then
        some { before := [], chosen := record, after := rest }
      else
        match firstEitherInputOccurrence outputInput advanceInput rest with
        | none => none
        | some occurrence => some
            { before := record :: occurrence.before
              chosen := occurrence.chosen
              after := occurrence.after }

theorem first_either_input_occurrence_spec
    (outputInput advanceInput : ShaInput) (records : List QueryRecord)
    (occurrence : PairOccurrenceSplit)
    (found : firstEitherInputOccurrence outputInput advanceInput records =
      some occurrence) :
    records = occurrence.before ++ occurrence.chosen :: occurrence.after ∧
    (∀ prior ∈ occurrence.before,
      prior.input ≠ outputInput ∧ prior.input ≠ advanceInput) ∧
    (occurrence.chosen.input = outputInput ∨
      occurrence.chosen.input = advanceInput) := by
  induction records generalizing occurrence with
  | nil => simp [firstEitherInputOccurrence] at found
  | cons record rest ih =>
      by_cases hit : record.input = outputInput ∨
        record.input = advanceInput
      · simp only [firstEitherInputOccurrence, hit, if_true,
          Option.some.injEq] at found
        cases found
        exact ⟨rfl, by simp, hit⟩
      · cases recursive : firstEitherInputOccurrence outputInput
          advanceInput rest with
        | none =>
            simp [firstEitherInputOccurrence, hit, recursive] at found
        | some tailOccurrence =>
            simp only [firstEitherInputOccurrence, hit, if_false, recursive,
              Option.some.injEq] at found
            cases found
            obtain ⟨decomposition, beforeFresh, chosen⟩ :=
              ih tailOccurrence recursive
            refine ⟨by simp [decomposition], ?_, chosen⟩
            intro prior member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact ⟨fun equal => hit (Or.inl equal),
                fun equal => hit (Or.inr equal)⟩
            · exact beforeFresh prior member

noncomputable def firstGeneratedPairOccurrenceInFrozenQ1
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (stateAtAdversaryHalt : OracleState)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) : Option PairOccurrenceSplit :=
  firstEitherInputOccurrence
    (generatedPairInput execution generated .output)
    (generatedPairInput execution generated .advance)
    (freezeAdversaryQ1 stateAtAdversaryHalt)

theorem first_generated_pair_occurrence_in_frozen_q1_is_exact
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (stateAtAdversaryHalt : OracleState)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (occurrence : PairOccurrenceSplit)
    (found : firstGeneratedPairOccurrenceInFrozenQ1 stateAtAdversaryHalt
      execution generated = some occurrence) :
    freezeAdversaryQ1 stateAtAdversaryHalt =
        occurrence.before ++ occurrence.chosen :: occurrence.after ∧
      (∀ prior ∈ occurrence.before,
        prior.input ≠ generatedPairInput execution generated .output ∧
        prior.input ≠ generatedPairInput execution generated .advance) ∧
      (occurrence.chosen.input =
          generatedPairInput execution generated .output ∨
        occurrence.chosen.input =
          generatedPairInput execution generated .advance) ∧
      occurrence.chosen.actor = .adversary := by
  have spec := first_either_input_occurrence_spec
    (generatedPairInput execution generated .output)
    (generatedPairInput execution generated .advance)
    (freezeAdversaryQ1 stateAtAdversaryHalt) occurrence found
  have chosenMember : occurrence.chosen ∈
      freezeAdversaryQ1 stateAtAdversaryHalt := by
    rw [spec.1]
    simp
  exact ⟨spec.1, spec.2.1, spec.2.2,
    frozen_q1_contains_only_adversary_calls stateAtAdversaryHalt
      occurrence.chosen chosenMember⟩

/-! ## Either half restores the same complete state -/

def restorationAtPairHalf
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (_half : SqueezeHalf) : ConcreteRestorationRecord table dag :=
  concreteRestoration execution generated

@[simp] theorem restoration_at_pair_output_eq_advance
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    restorationAtPairHalf execution generated .output =
      restorationAtPairHalf execution generated .advance := by
  rfl

theorem either_pair_half_restores_same_complete_seen_bound_state
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag) :
    let outputRestoration :=
      restorationAtPairHalf execution generated .output
    let advanceRestoration :=
      restorationAtPairHalf execution generated .advance
    outputRestoration = advanceRestoration ∧
      IsComplete outputRestoration.snapshot ∧
      PreviouslySeen outputRestoration.snapshot
        outputRestoration.sourceExecution.interactiveState ∧
      NonemptyVerifierHistory
        outputRestoration.sourceExecution.interactiveState ∧
      outputRestoration.snapshot.bindings.programId =
          dag.tape.messages.context.programId ∧
      outputRestoration.snapshot.bindings.releaseBinding =
          dag.tape.messages.context.releaseBinding ∧
      outputRestoration.snapshot.bindings.statementDigest =
          dag.tape.messages.context.statementDigest ∧
      outputRestoration.snapshot.bindings.attemptId =
          dag.tape.messages.context.attemptId ∧
      outputRestoration.snapshot.bindings.proofAccountId =
          dag.tape.messages.context.attemptId := by
  let restoration := concreteRestoration execution generated
  have bindings :=
    restoration_preserves_program_release_statement_attempt_account restoration
  exact ⟨rfl, restoration_snapshot_is_complete restoration,
    restoration_snapshot_is_previously_seen restoration,
    restoration_first_run_history_is_nonempty restoration,
    bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2.1,
    bindings.2.2.2.2⟩

#print axioms generated_pair_is_exact_next_action_input_list
#print axioms generated_pair_uses_one_pre_action_state
#print axioms generated_pair_inputs_are_distinct
#print axioms first_either_input_occurrence_spec
#print axioms first_generated_pair_occurrence_in_frozen_q1_is_exact
#print axioms restoration_at_pair_output_eq_advance
#print axioms either_pair_half_restores_same_complete_seen_bound_state

end AspisK1.V7Tag73AtomicPairFork
