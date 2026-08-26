import AspisFormal.K1.V7Tag73InteractiveAncestor

/-!
# Concrete table-driven execution of the Tag-73 interactive ancestor

This file runs the literal `fullPlan` against one fixed finite oracle table.
Replies are derived from `actionInputs`; they are never supplied by an abstract
restore or trace-cover interface.  A paired squeeze performs both table
lookups at the same pre-action digest and yields one atomic `VerifierReply`.

The executable trace is indexed by its starting core and exact remaining
action list.  Consequently, the first-execution history, state at every cursor,
and transition order are all derived data.  Missing table entries or a reply
that cannot be applied make construction return `none`.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73InteractiveExecution

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor

/-! ## Replies derived from the exact table inputs -/

def lookupSingleInput (table : FixedOracleTable) :
    List ByteString → Option Digest256
  | [input] => tableLookup table input
  | _ => none

/-- Derive the unique reply shape appropriate for an action.  Structural
actions have no table call.  Every ordinary hash action has exactly one input;
a squeeze must expose exactly its two paired inputs. -/
def deriveReply (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (action : VerifierAction) : Option VerifierReply :=
  match action with
  | .checkpoint _ | .markQ16Base | .q16Restore _ | .q16Selected _ |
      .q16SamplerAbortReject _ | .q16AllNoncompactReject | .terminal =>
      some .none
  | .squeezePair _ _ =>
      match actionInputs bindings core action with
      | [outputInput, advanceInput] => do
          let output ← tableLookup table outputInput
          let advance ← tableLookup table advanceInput
          pure (.squeeze output advance)
      | _ => none
  | _ => do
      let output ← lookupSingleInput table (actionInputs bindings core action)
      pure (.single output)

theorem derive_squeeze_reply_iff
    (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (owner : SqueezeOwner) (block : Nat)
    (output advance : Digest256) :
    deriveReply table bindings core (.squeezePair owner block) =
        some (.squeeze output advance) ↔
      tableLookup table (bytes core.digest ++ [domSqueeze]) = some output ∧
      tableLookup table (bytes core.digest ++ [domAdvance]) = some advance := by
  cases first : tableLookup table (bytes core.digest ++ [domSqueeze]) with
  | none => simp [deriveReply, actionInputs, first]
  | some firstOutput =>
      cases second : tableLookup table (bytes core.digest ++ [domAdvance]) with
      | none => simp [deriveReply, actionInputs, first, second]
      | some advanceOutput =>
          simp [deriveReply, actionInputs, first, second]

theorem derived_squeeze_uses_two_distinct_same_state_inputs
    (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (owner : SqueezeOwner) (block : Nat)
    (reply : VerifierReply)
    (derived : deriveReply table bindings core (.squeezePair owner block) =
      some reply) :
    ∃ output advance,
      reply = .squeeze output advance ∧
      tableLookup table (bytes core.digest ++ [1]) = some output ∧
      tableLookup table (bytes core.digest ++ [2]) = some advance ∧
      bytes core.digest ++ [1] ≠ bytes core.digest ++ [2] := by
  cases first : tableLookup table (bytes core.digest ++ [domSqueeze]) with
  | none => simp [deriveReply, actionInputs, first] at derived
  | some output =>
      cases second : tableLookup table (bytes core.digest ++ [domAdvance]) with
      | none => simp [deriveReply, actionInputs, first, second] at derived
      | some advance =>
          simp [deriveReply, actionInputs, first, second] at derived
          subst reply
          exact ⟨output, advance, rfl, first, second,
            squeeze_output_and_advance_inputs_are_distinct core.digest⟩

/-! ## A dependent executable trace -/

/-- This is operational evidence produced by `buildTrace`.  Its equality
fields certify one concrete table lookup and one concrete ancestor transition;
they state no acceptance, extraction, or compiler conclusion. -/
inductive TableExecutionTrace (table : FixedOracleTable)
    (bindings : FixedBindings) :
    RuntimeCore → List VerifierAction → Type where
  | done (core : RuntimeCore) : TableExecutionTrace table bindings core []
  | step {core next : RuntimeCore} {action : VerifierAction}
      {rest : List VerifierAction}
      (reply : VerifierReply)
      (derived : deriveReply table bindings core action = some reply)
      (applied : applyActionWorkErased core action reply = some next)
      (tail : TableExecutionTrace table bindings next rest) :
      TableExecutionTrace table bindings core (action :: rest)

def buildTrace (table : FixedOracleTable) (bindings : FixedBindings) :
    (core : RuntimeCore) → (actions : List VerifierAction) →
      Option (TableExecutionTrace table bindings core actions)
  | core, [] => some (.done core)
  | core, action :: rest =>
      match hreply : deriveReply table bindings core action with
      | none => none
      | some reply =>
          match hnext : applyActionWorkErased core action reply with
          | none => none
          | some next =>
              match buildTrace table bindings next rest with
              | none => none
              | some tail => some (.step reply hreply hnext tail)

def TableExecutionTrace.cores
    {table : FixedOracleTable} {bindings : FixedBindings}
    {core : RuntimeCore} {actions : List VerifierAction}
    (trace : TableExecutionTrace table bindings core actions) :
    List RuntimeCore :=
  match trace with
  | .done _ => [core]
  | .step _ _ _ tail => core :: tail.cores

def TableExecutionTrace.replies
    {table : FixedOracleTable} {bindings : FixedBindings}
    {core : RuntimeCore} {actions : List VerifierAction}
    (trace : TableExecutionTrace table bindings core actions) :
    List VerifierReply :=
  match trace with
  | .done _ => []
  | .step reply _ _ tail => reply :: tail.replies

def TableExecutionTrace.actionReplies
    {table : FixedOracleTable} {bindings : FixedBindings}
    {core : RuntimeCore} {actions : List VerifierAction}
    (trace : TableExecutionTrace table bindings core actions) :
    List (VerifierAction × VerifierReply) :=
  match trace with
  | .done _ => []
  | @TableExecutionTrace.step _ _ _ _ action _ reply _ _ tail =>
      (action, reply) :: tail.actionReplies

@[simp] theorem trace_cores_length
    {table : FixedOracleTable} {bindings : FixedBindings}
    {core : RuntimeCore} {actions : List VerifierAction}
    (trace : TableExecutionTrace table bindings core actions) :
    trace.cores.length = actions.length + 1 := by
  induction trace with
  | done => simp [TableExecutionTrace.cores]
  | step reply derived applied tail ih =>
      simp [TableExecutionTrace.cores, ih]

@[simp] theorem trace_replies_length
    {table : FixedOracleTable} {bindings : FixedBindings}
    {core : RuntimeCore} {actions : List VerifierAction}
    (trace : TableExecutionTrace table bindings core actions) :
    trace.replies.length = actions.length := by
  induction trace with
  | done => simp [TableExecutionTrace.replies]
  | step reply derived applied tail ih =>
      simp [TableExecutionTrace.replies, ih]

@[simp] theorem trace_action_replies_length
    {table : FixedOracleTable} {bindings : FixedBindings}
    {core : RuntimeCore} {actions : List VerifierAction}
    (trace : TableExecutionTrace table bindings core actions) :
    trace.actionReplies.length = actions.length := by
  induction trace with
  | done => simp [TableExecutionTrace.actionReplies]
  | step reply derived applied tail ih =>
      simp [TableExecutionTrace.actionReplies, ih]

theorem trace_action_reply_actions_are_literal_plan
    {table : FixedOracleTable} {bindings : FixedBindings}
    {core : RuntimeCore} {actions : List VerifierAction}
    (trace : TableExecutionTrace table bindings core actions) :
    trace.actionReplies.map Prod.fst = actions := by
  induction trace with
  | done => rfl
  | step reply derived applied tail ih =>
      simp [TableExecutionTrace.actionReplies, ih]

def ReplyCompletesAction (action : VerifierAction)
    (reply : VerifierReply) : Prop :=
  match action with
  | .squeezePair _ _ => ∃ output advance, reply = .squeeze output advance
  | _ => True

theorem derived_reply_completes_action
    (table : FixedOracleTable) (bindings : FixedBindings)
    (core : RuntimeCore) (action : VerifierAction) (reply : VerifierReply)
    (derived : deriveReply table bindings core action = some reply) :
    ReplyCompletesAction action reply := by
  cases action <;> simp [ReplyCompletesAction]
  case squeezePair owner block =>
    obtain ⟨output, advance, equals, _⟩ :=
      derived_squeeze_uses_two_distinct_same_state_inputs
        table bindings core owner block reply derived
    exact ⟨output, advance, equals⟩

theorem trace_contains_no_half_squeeze_reply
    {table : FixedOracleTable} {bindings : FixedBindings}
    {core : RuntimeCore} {actions : List VerifierAction}
    (trace : TableExecutionTrace table bindings core actions) :
    ∀ pair ∈ trace.actionReplies,
      ReplyCompletesAction pair.1 pair.2 := by
  induction trace with
  | done => simp [TableExecutionTrace.actionReplies]
  | @step core next action rest reply derived applied tail ih =>
      intro pair member
      simp only [TableExecutionTrace.actionReplies, List.mem_cons] at member
      rcases member with rfl | member
      · exact derived_reply_completes_action _ _ _ _ _ derived
      · exact ih pair member

/-! ## The literal deployed first execution -/

structure ConcreteFirstExecution (table : FixedOracleTable)
    (tape : DeployedFixedTape) where
  trace : TableExecutionTrace table
    (FixedBindings.ofContext tape.messages.context)
    initialCore (fullPlan tape)

def executeFirst (table : FixedOracleTable) (tape : DeployedFixedTape) :
    Option (ConcreteFirstExecution table tape) :=
  (buildTrace table (FixedBindings.ofContext tape.messages.context)
    initialCore (fullPlan tape)).map ConcreteFirstExecution.mk

def ConcreteFirstExecution.table
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (_execution : ConcreteFirstExecution table tape) : FixedOracleTable := table

def ConcreteFirstExecution.tape
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (_execution : ConcreteFirstExecution table tape) : DeployedFixedTape := tape

@[simp] theorem first_execution_retains_same_table
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    execution.table = table := by
  rfl

@[simp] theorem first_execution_retains_same_tape
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    execution.tape = tape := by
  rfl

def ConcreteFirstExecution.cores
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) : List RuntimeCore :=
  execution.trace.cores

def ConcreteFirstExecution.coreAt
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape)
    (cursor : Fin (fullPlan tape).length.succ) : RuntimeCore :=
  execution.cores.get
    ⟨cursor.val, by simpa [ConcreteFirstExecution.cores] using cursor.isLt⟩

/-- The state at a cursor is read from the generated core history.  No caller
supplies a state function. -/
def ConcreteFirstExecution.stateAtCursor
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape)
    (cursor : Fin (fullPlan tape).length.succ) : CompleteSnapshot tape where
  cursor := cursor
  core := execution.coreAt cursor

def ConcreteFirstExecution.seen
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    List (CompleteSnapshot tape) :=
  List.ofFn execution.stateAtCursor

def ConcreteFirstExecution.replyAt
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape)
    (index : Fin (fullPlan tape).length) : VerifierReply :=
  execution.trace.replies.get
    ⟨index.val, by simpa using index.isLt⟩

def ConcreteFirstExecution.transitionAt
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape)
    (index : Fin (fullPlan tape).length) : TransitionRecord tape :=
  let beforeCursor : Fin (fullPlan tape).length.succ :=
    ⟨index.val, Nat.lt.step index.isLt⟩
  let afterCursor : Fin (fullPlan tape).length.succ :=
    ⟨index.val + 1, by omega⟩
  let action := (fullPlan tape).get index
  let reply := execution.replyAt index
  { before := execution.stateAtCursor beforeCursor
    action := action
    reply := reply
    inputs := actionInputs
      (FixedBindings.ofContext tape.messages.context)
      (execution.stateAtCursor beforeCursor).core action
    after := execution.stateAtCursor afterCursor }

def ConcreteFirstExecution.transitions
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    List (TransitionRecord tape) :=
  List.ofFn execution.transitionAt

def finalCursor (tape : DeployedFixedTape) :
    Fin (fullPlan tape).length.succ :=
  ⟨(fullPlan tape).length, Nat.lt_succ_self _⟩

def ConcreteFirstExecution.interactiveState
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    InteractiveVerifierState tape where
  current := execution.stateAtCursor (finalCursor tape)
  seen := execution.seen
  transitions := execution.transitions

@[simp] theorem first_execution_core_history_length
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    execution.cores.length = (fullPlan tape).length + 1 := by
  exact trace_cores_length execution.trace

@[simp] theorem first_execution_seen_length
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    execution.seen.length = (fullPlan tape).length + 1 := by
  simp [ConcreteFirstExecution.seen]

@[simp] theorem first_execution_transition_length
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    execution.transitions.length = (fullPlan tape).length := by
  simp [ConcreteFirstExecution.transitions]

theorem first_execution_history_is_nonempty
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    execution.seen ≠ [] := by
  intro empty
  have lengths := congrArg List.length empty
  simp [first_execution_seen_length] at lengths

theorem state_at_cursor_is_complete
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape)
    (cursor : Fin (fullPlan tape).length.succ) :
    IsComplete (execution.stateAtCursor cursor) :=
  every_typed_snapshot_is_complete _

theorem state_at_cursor_is_in_first_run_history
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape)
    (cursor : Fin (fullPlan tape).length.succ) :
    execution.stateAtCursor cursor ∈ execution.seen := by
  rw [ConcreteFirstExecution.seen, List.mem_ofFn]
  exact ⟨cursor, rfl⟩

theorem state_at_cursor_is_previously_seen
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape)
    (cursor : Fin (fullPlan tape).length.succ) :
    PreviouslySeen (execution.stateAtCursor cursor)
      execution.interactiveState := by
  exact state_at_cursor_is_in_first_run_history execution cursor

theorem every_cursor_has_constant_bindings
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape)
    (cursor : Fin (fullPlan tape).length.succ) :
    (execution.stateAtCursor cursor).bindings =
      FixedBindings.ofContext tape.messages.context := by
  rfl

theorem dummy_initial_state_is_retained
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    (execution.stateAtCursor ⟨0, Nat.zero_lt_succ _⟩).phase =
        .dummyNonempty ∧
      execution.stateAtCursor ⟨0, Nat.zero_lt_succ _⟩ ∈ execution.seen := by
  exact ⟨by simp [CompleteSnapshot.phase, phaseForCursor,
    ConcreteFirstExecution.stateAtCursor],
    state_at_cursor_is_in_first_run_history execution _⟩

/-- In the generated transition history, a squeeze reply always contains both
the output and advance answers.  Therefore no cursor is inserted between the
two lookups. -/
theorem first_execution_has_no_half_squeeze_reply
    {table : FixedOracleTable} {tape : DeployedFixedTape}
    (execution : ConcreteFirstExecution table tape) :
    ∀ pair ∈ execution.trace.actionReplies,
      ReplyCompletesAction pair.1 pair.2 :=
  trace_contains_no_half_squeeze_reply execution.trace

#print axioms derive_squeeze_reply_iff
#print axioms derived_squeeze_uses_two_distinct_same_state_inputs
#print axioms trace_cores_length
#print axioms trace_action_reply_actions_are_literal_plan
#print axioms trace_contains_no_half_squeeze_reply
#print axioms first_execution_core_history_length
#print axioms first_execution_seen_length
#print axioms state_at_cursor_is_complete
#print axioms state_at_cursor_is_in_first_run_history
#print axioms dummy_initial_state_is_retained
#print axioms first_execution_has_no_half_squeeze_reply

end AspisK1.V7Tag73InteractiveExecution
