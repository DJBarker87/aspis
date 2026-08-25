import AspisFormal.K1.V7Tag73UniformOracleBoundary
import AspisFormal.K1.V7Tag73ConcreteStateRestoration

/-!
# Operational fresh-answer exposure for Tag 73

This module connects the finite uniform tape to the executable lazy oracle.
Fresh answers are enumerated from the actual ordered `QueryRecord` history,
not supplied as an unrelated list.  A controller closes over one finite tape
and selects the next answer using the number of `.fresh` records already in
that history.  Successful oracle calls and complete `runMachine` executions
preserve both the exact fresh-record counter and the hard tape-length bound.

The module also eliminates two deterministic event classes without a
probability assumption:

* every concrete generated Tag-73 restoration carries exactly the fixed
  program/release/statement/attempt/proof-account bindings; and
* every concrete resource ledger fits an envelope constructed from its
  literal fields and restoration sums.

The second construction is an exact post-execution accounting certificate,
not an ex-ante runtime claim and not a full-256 exposure certificate.  Its
`full256FreshExposures` field is deliberately zero: separating shared SHA
calls from typed 208-bit Merkle computations still requires the operational
domain bridge described in `V7Tag73UniformOracleBoundary`.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73OperationalOracleExposure

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73UniformOracleBoundary
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73ConcreteStateRestoration

noncomputable section

/-! ## Fresh answers extracted from the actual ordered history -/

/-- The full 256-bit answers exposed freshly by a concrete query history, in
call order.  Cached and programmed answers are not fresh exposures. -/
def freshAnswerEnumeration : List QueryRecord → List Digest256
  | [] => []
  | record :: rest =>
      match record.origin with
      | .fresh => record.output :: freshAnswerEnumeration rest
      | .programmed => freshAnswerEnumeration rest
      | .cached => freshAnswerEnumeration rest

@[simp] theorem fresh_answer_enumeration_append
    (first second : List QueryRecord) :
    freshAnswerEnumeration (first ++ second) =
      freshAnswerEnumeration first ++ freshAnswerEnumeration second := by
  induction first with
  | nil => rfl
  | cons record rest ih =>
      rcases record with ⟨input, output, actor, origin⟩
      cases origin <;> simp [freshAnswerEnumeration, ih]

@[simp] theorem fresh_answer_enumeration_fresh_singleton
    (input : ShaInput) (output : ShaOutput) (actor : QueryActor) :
    freshAnswerEnumeration
        [{ input := input, output := output, actor := actor,
           origin := .fresh }] =
      [output] := by
  rfl

@[simp] theorem fresh_answer_enumeration_programmed_singleton
    (input : ShaInput) (output : ShaOutput) (actor : QueryActor) :
    freshAnswerEnumeration
        [{ input := input, output := output, actor := actor,
           origin := .programmed }] =
      [] := by
  rfl

@[simp] theorem fresh_answer_enumeration_cached_singleton
    (input : ShaInput) (output : ShaOutput) (actor : QueryActor) :
    freshAnswerEnumeration
        [{ input := input, output := output, actor := actor,
           origin := .cached }] =
      [] := by
  rfl

/-- Operational coherence between `OracleState.freshCalls` and the records
actually marked fresh in its ordered history. -/
def FreshHistoryCountCoherent (state : OracleState) : Prop :=
  (freshAnswerEnumeration state.history).length = state.freshCalls

theorem empty_oracle_fresh_history_count_coherent :
    FreshHistoryCountCoherent emptyOracle := by
  rfl

/-- Any successful executable oracle call preserves the exact fresh-history
counter.  In the cached branch the enumeration is unchanged; in the missing
input branch one `.fresh` record and one fresh call are appended together. -/
theorem query_oracle_success_preserves_fresh_history_count
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (coherent : FreshHistoryCountCoherent state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    FreshHistoryCountCoherent nextState := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      unfold FreshHistoryCountCoherent at coherent ⊢
      rw [fresh_answer_enumeration_append]
      cases entry.source <;>
        simp [cachedOrigin, freshAnswerEnumeration, coherent]
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next _ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          unfold FreshHistoryCountCoherent at coherent ⊢
          rw [fresh_answer_enumeration_append]
          simp [freshAnswerEnumeration, coherent]

/-- Full machine execution preserves the counter invariant from its supplied
initial oracle, including oracle-abort and fuel-exhaustion exits. -/
theorem run_machine_preserves_fresh_history_count
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (coherent : FreshHistoryCountCoherent state) :
    FreshHistoryCountCoherent
      (runMachine controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> simp [runMachine, coherent]
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runMachine] using coherent
      | abort reason => simpa [runMachine] using coherent
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle controller limits actor state input with
          | error reason => simpa using coherent
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextCoherent :=
                query_oracle_success_preserves_fresh_history_count
                  controller limits actor state nextState input output coherent
                    queryResult
              simpa using ih nextState (next output) nextCoherent

/-! ## A concrete uniform fresh-answer controller -/

/-- Flatten the inductive finite tape in the same left-to-right order in which
the controller exposes answers. -/
def freshAnswerTapeToList {Output : Type} :
    ∀ {steps : Nat}, FreshAnswerTape Output steps → List Output
  | 0, _ => []
  | _ + 1, tape => tape.1 :: freshAnswerTapeToList tape.2

@[simp] theorem fresh_answer_tape_to_list_length
    {Output : Type} {steps : Nat}
    (tape : FreshAnswerTape Output steps) :
    (freshAnswerTapeToList tape).length = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      change (tape.1 :: freshAnswerTapeToList tape.2).length = steps + 1
      simp [ih]

/-- A deterministic controller backed by one fixed fresh-answer tape.  Its
only index is computed from the actual ordered history. -/
def controllerFromFreshAnswerTape {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) : AdaptiveController :=
  fun history _input =>
    if available : (freshAnswerEnumeration history).length <
        (freshAnswerTapeToList tape).length then
      .answer ((freshAnswerTapeToList tape).get
        ⟨(freshAnswerEnumeration history).length, available⟩)
    else
      .refuse

theorem controller_answer_implies_exposure_available
    {steps : Nat} (tape : FreshAnswerTape Digest256 steps)
    (history : List QueryRecord) (input : ShaInput) (output : ShaOutput)
    (answered : controllerFromFreshAnswerTape tape history input =
      .answer output) :
    (freshAnswerEnumeration history).length < steps := by
  unfold controllerFromFreshAnswerTape at answered
  split at answered
  next available =>
    simpa [fresh_answer_tape_to_list_length] using available
  next _ => contradiction

theorem controller_refuses_after_all_exposures
    {steps : Nat} (tape : FreshAnswerTape Digest256 steps)
    (history : List QueryRecord)
    (exhausted : steps ≤ (freshAnswerEnumeration history).length)
    (input : ShaInput) :
    controllerFromFreshAnswerTape tape history input = .refuse := by
  unfold controllerFromFreshAnswerTape
  split
  next available =>
    rw [fresh_answer_tape_to_list_length] at available
    omega
  next _ => rfl

/-- In addition to exact counter coherence, an execution backed by a finite
tape can never record more fresh answers than the tape contains. -/
def WithinFreshAnswerTape {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) (state : OracleState) : Prop :=
  FreshHistoryCountCoherent state ∧ state.freshCalls ≤ steps

theorem empty_oracle_within_fresh_answer_tape
    {steps : Nat} (tape : FreshAnswerTape Digest256 steps) :
    WithinFreshAnswerTape tape emptyOracle := by
  exact ⟨empty_oracle_fresh_history_count_coherent, Nat.zero_le steps⟩

/-- A successful call made with the concrete tape controller preserves the
hard fresh-exposure cap.  The bound follows from the controller's actual
history index, not from `OracleLimits.freshCalls`. -/
theorem tape_query_success_preserves_fresh_exposure_bound
    {steps : Nat} (tape : FreshAnswerTape Digest256 steps)
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (input : ShaInput) (output : ShaOutput)
    (within : WithinFreshAnswerTape tape state)
    (success : queryOracle (controllerFromFreshAnswerTape tape) limits actor
      state input = .ok (output, nextState)) :
    WithinFreshAnswerTape tape nextState := by
  have nextCoherent := query_oracle_success_preserves_fresh_history_count
    (controllerFromFreshAnswerTape tape) limits actor state nextState input
      output within.1 success
  refine ⟨nextCoherent, ?_⟩
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact within.2
    next missing =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next refused => contradiction
        next answer answered =>
          have available := controller_answer_implies_exposure_available
            tape state.history input answer answered
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          have coherent := within.1
          unfold FreshHistoryCountCoherent at coherent
          change state.freshCalls + 1 ≤ steps
          omega

/-- Complete executable runs under the tape controller satisfy both exact
fresh-record counting and the global cap `freshCalls ≤ steps`. -/
theorem run_machine_with_uniform_tape_preserves_exposure_bound
    {Result : Type*} {steps : Nat}
    (tape : FreshAnswerTape Digest256 steps) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (within : WithinFreshAnswerTape tape state) :
    WithinFreshAnswerTape tape
      (runMachine (controllerFromFreshAnswerTape tape) limits actor fuel state
        program).oracle := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> simp [runMachine, within]
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runMachine] using within
      | abort reason => simpa [runMachine] using within
      | query input next =>
          simp only [runMachine]
          cases queryResult : queryOracle (controllerFromFreshAnswerTape tape)
              limits actor state input with
          | error reason => simpa using within
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextWithin :=
                tape_query_success_preserves_fresh_exposure_bound tape limits
                  actor state nextState input output within queryResult
              simpa using ih nextState (next output) nextWithin

/-- The actual machine-valued experiment over a uniform tape.  Unlike
`ObservedProofExperiment.law`, its source of fresh answers is fixed by
construction. -/
def runMachineFromUniformFreshTape
    {Result : Type*} (steps : Nat) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (program : OracleMachine Result) :
    FreshAnswerTape Digest256 steps → MachineRun Result :=
  fun tape => runMachine (controllerFromFreshAnswerTape tape) limits actor fuel
    emptyOracle program

theorem uniform_tape_machine_fresh_exposure_bound
    {Result : Type*} (steps : Nat) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (program : OracleMachine Result)
    (tape : FreshAnswerTape Digest256 steps) :
    FreshHistoryCountCoherent
        (runMachineFromUniformFreshTape steps limits actor fuel program tape).oracle ∧
      (runMachineFromUniformFreshTape steps limits actor fuel program tape).oracle.freshCalls
        ≤ steps := by
  exact run_machine_with_uniform_tape_preserves_exposure_bound tape limits actor
    fuel emptyOracle program (empty_oracle_within_fresh_answer_tape tape)

/-- The concrete pushforward law of the executable run.  This definition is
the missing probabilistic ingredient that an arbitrary
`ObservedProofExperiment.law` does not provide: its source measure is exactly
the uniform PMF on `Q` complete fresh 256-bit answer tapes. -/
noncomputable def uniformFreshOracleMachineLaw
    {Result : Type*} (steps : Nat) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (program : OracleMachine Result) :
    PMF (MachineRun Result) :=
  (uniformDigestFreshTape steps).map
    (runMachineFromUniformFreshTape steps limits actor fuel program)

theorem uniform_fresh_oracle_machine_law_event_probability
    {Result : Type*} (steps : Nat) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (program : OracleMachine Result)
    (event : Set (MachineRun Result)) :
    (uniformFreshOracleMachineLaw steps limits actor fuel program).toOuterMeasure
        event =
      (uniformDigestFreshTape steps).toOuterMeasure
        (runMachineFromUniformFreshTape steps limits actor fuel program ⁻¹'
          event) := by
  exact PMF.toOuterMeasure_map_apply _ _ _

/-- A concrete event on machine outputs, not a field of an experiment. -/
def FreshExposureOverflowEvent {Result : Type*} (steps : Nat) :
    Set (MachineRun Result) :=
  {run | steps < run.oracle.freshCalls}

/-- Under the explicit uniform-tape execution law, exceeding the supplied
fresh-answer tape has probability zero.  This is deterministic exhaustion,
not a random-oracle collision estimate. -/
theorem uniform_fresh_oracle_machine_overflow_probability_zero
    {Result : Type*} (steps : Nat) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (program : OracleMachine Result) :
    (uniformFreshOracleMachineLaw steps limits actor fuel program).toOuterMeasure
        (FreshExposureOverflowEvent steps) = 0 := by
  rw [uniform_fresh_oracle_machine_law_event_probability]
  have emptyPreimage :
      runMachineFromUniformFreshTape steps limits actor fuel program ⁻¹'
          FreshExposureOverflowEvent steps = ∅ := by
    ext tape
    have bounded :=
      (uniform_tape_machine_fresh_exposure_bound
        steps limits actor fuel program tape).2
    simp only [Set.mem_preimage, FreshExposureOverflowEvent, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false]
    omega
  rw [emptyPreimage]
  simp

/-! ## Concrete fixed-binding failure is impossible -/

/-- A failure event over actual restoration records, rather than an arbitrary
replayed-context function. -/
noncomputable def concreteRestorationBindingFailureEvent
    {Sample : Type*} {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (restoration : Sample → ConcreteRestorationRecord table dag) : Set Sample :=
  {sample |
    (restoration sample).snapshot.bindings ≠
      FixedBindings.ofContext dag.tape.messages.context}

theorem concrete_restoration_binding_failure_event_empty
    {Sample : Type*} {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (restoration : Sample → ConcreteRestorationRecord table dag) :
    concreteRestorationBindingFailureEvent restoration = ∅ := by
  ext sample
  simp [concreteRestorationBindingFailureEvent,
    restoration_preserves_fixed_bindings (restoration sample)]

/-! ## Exact deterministic resource-accounting certificate -/

/-- An envelope computed from a concrete completed ledger.  Per-restoration
caps are the corresponding literal sums, so every individual restoration is
bounded without a maximum/default convention.  The final field is zero
because this definition does not classify typed Merkle calls as full-output
fresh exposures. -/
def exactAccountingEnvelope
    (ledger : StrictTag73ResourceLedger) : StrictTag73ResourceEnvelope where
  q1Calls := ledger.q1.length
  verifierOracleCalls := ledger.verifierOracleCalls
  restorationCount := ledger.restorations.length
  oracleCallsPerRestoration := restorationOracleCalls ledger
  firstRunRuntimeSteps := ledger.firstRunRuntimeSteps
  verifierRuntimeSteps := ledger.verifierRuntimeSteps
  runtimeStepsPerRestoration := restorationRuntimeSteps ledger
  freshOracleAnswers := ledger.freshOracleAnswers
  programmedPoints := ledger.programmedPoints
  batchGrindingQueries := ledger.batchGrindingQueries
  foldGrindingQueries := ledger.foldGrindingQueries
  finalGrindingQueries := ledger.finalGrindingQueries
  queryCandidateBranches := ledger.queryCandidateBranches
  full256FreshExposures := 0

theorem strict_ledger_within_exact_accounting_envelope
    (ledger : StrictTag73ResourceLedger) :
    WithinBudget (strictTag73ResourceUse ledger)
      (strictTag73ResourceBudget (exactAccountingEnvelope ledger)) := by
  apply strict_resource_ledger_within_envelope ledger
    (exactAccountingEnvelope ledger)
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · intro cost member
    unfold exactAccountingEnvelope
    unfold restorationOracleCalls
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨cost, member, rfl⟩)
  · exact le_rfl
  · exact le_rfl
  · intro cost member
    unfold exactAccountingEnvelope
    unfold restorationRuntimeSteps
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨cost, member, rfl⟩)
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

def exactAccountingResourceFailureEvent
    {Sample : Type*} (ledger : Sample → StrictTag73ResourceLedger) : Set Sample :=
  {sample |
    ¬ WithinBudget (strictTag73ResourceUse (ledger sample))
      (strictTag73ResourceBudget (exactAccountingEnvelope (ledger sample)))}

theorem exact_accounting_resource_failure_event_empty
    {Sample : Type*} (ledger : Sample → StrictTag73ResourceLedger) :
    exactAccountingResourceFailureEvent ledger = ∅ := by
  ext sample
  simp [exactAccountingResourceFailureEvent,
    strict_ledger_within_exact_accounting_envelope (ledger sample)]

#print axioms fresh_answer_enumeration_append
#print axioms query_oracle_success_preserves_fresh_history_count
#print axioms run_machine_preserves_fresh_history_count
#print axioms fresh_answer_tape_to_list_length
#print axioms controller_answer_implies_exposure_available
#print axioms controller_refuses_after_all_exposures
#print axioms tape_query_success_preserves_fresh_exposure_bound
#print axioms run_machine_with_uniform_tape_preserves_exposure_bound
#print axioms uniform_tape_machine_fresh_exposure_bound
#print axioms uniform_fresh_oracle_machine_law_event_probability
#print axioms uniform_fresh_oracle_machine_overflow_probability_zero
#print axioms concrete_restoration_binding_failure_event_empty
#print axioms strict_ledger_within_exact_accounting_envelope
#print axioms exact_accounting_resource_failure_event_empty

end

end AspisK1.V7Tag73OperationalOracleExposure
