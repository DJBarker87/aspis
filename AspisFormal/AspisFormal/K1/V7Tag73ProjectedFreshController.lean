import AspisFormal.K1.V7Tag73AtomicForkUniformScheduler

/-!
# Controller reconstructed from scheduler machine-fresh exposures

The unified master tape interleaves lazy-oracle answers with the two uniform
coordinates of every programmed fork.  Consequently the master tape itself
cannot be passed to `controllerFromFreshAnswerTape`: doing so would consume
fork coordinates as oracle answers.

This leaf defines the exact projection that keeps only `.machineFresh`
answers and a deterministic controller indexed by the actual fresh records
appended after one initial history.  Its one-step theorem is the local bridge
needed to prove that a result-carrying scheduler run can be replayed by an
ordinary `runMachine` without assuming an independently chosen controller.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ProjectedFreshController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler

noncomputable section

/-- Retain only actual lazy-oracle answers.  Fork output/advance coordinates
and inert terminal padding are deliberately excluded. -/
def machineFreshAnswers : List UnifiedExposureRecord → List Digest256
  | [] => []
  | .machineFresh _actor _input answer :: rest =>
      answer :: machineFreshAnswers rest
  | _record :: rest => machineFreshAnswers rest

/-- Exact pending inputs paired with their scheduler-supplied fresh answers.
The actor is retained by each `UnifiedExposureRecord`; a machine segment has
one fixed actor in `ProjectedFreshReturnedTrace`. -/
def machineFreshQueryAnswers :
    List UnifiedExposureRecord → List (ShaInput × Digest256)
  | [] => []
  | .machineFresh _actor input answer :: rest =>
      (input, answer) :: machineFreshQueryAnswers rest
  | _record :: rest => machineFreshQueryAnswers rest

@[simp] theorem machine_fresh_query_answers_append
    (first second : List UnifiedExposureRecord) :
    machineFreshQueryAnswers (first ++ second) =
      machineFreshQueryAnswers first ++ machineFreshQueryAnswers second := by
  induction first with
  | nil => rfl
  | cons record rest ih =>
      cases record <;> simp [machineFreshQueryAnswers, ih]

theorem machine_fresh_answers_eq_query_answers_map
    (records : List UnifiedExposureRecord) :
    machineFreshAnswers records =
      (machineFreshQueryAnswers records).map Prod.snd := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      cases record <;>
        simp [machineFreshAnswers, machineFreshQueryAnswers, ih]

@[simp] theorem machine_fresh_answers_append
    (first second : List UnifiedExposureRecord) :
    machineFreshAnswers (first ++ second) =
      machineFreshAnswers first ++ machineFreshAnswers second := by
  induction first with
  | nil => rfl
  | cons record rest ih =>
      cases record <;> simp [machineFreshAnswers, ih]

@[simp] theorem machine_fresh_answers_padding
    (answer : Digest256) (rest : List UnifiedExposureRecord) :
    machineFreshAnswers (.padding answer :: rest) =
      machineFreshAnswers rest := by
  rfl

@[simp] theorem machine_fresh_answers_fork_output
    (history : List QueryRecord) (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration) (answer : Digest256)
    (rest : List UnifiedExposureRecord) :
    machineFreshAnswers
      (.forkOutput history outputInput advanceInput template answer :: rest) =
        machineFreshAnswers rest := by
  rfl

@[simp] theorem machine_fresh_answers_fork_advance
    (scheduled : ScheduledForkCoins) (rest : List UnifiedExposureRecord) :
    machineFreshAnswers (.forkAdvance scheduled :: rest) =
      machineFreshAnswers rest := by
  rfl

@[simp] theorem machine_fresh_answers_machine_fresh
    (actor : QueryActor) (input : ShaInput) (answer : Digest256)
    (rest : List UnifiedExposureRecord) :
    machineFreshAnswers (.machineFresh actor input answer :: rest) =
      answer :: machineFreshAnswers rest := by
  rfl

/-- Number of fresh oracle answers consumed after the fixed initial history.
The subtraction-free definition uses the literal appended-history suffix. -/
def appendedFreshAnswerCount (initialHistory history : List QueryRecord) : Nat :=
  (freshAnswerEnumeration (history.drop initialHistory.length)).length

/-- The single controller reconstructed from the scheduler's projected fresh
answer list.  It is total: malformed/non-prefix histories or exhaustion return
`refuse` and are exposed by the later refinement theorem. -/
def controllerFromProjectedFreshAnswers
    (initialHistory : List QueryRecord) (answers : List Digest256) :
    AdaptiveController :=
  fun history _input =>
    match answers[appendedFreshAnswerCount initialHistory history]? with
    | some answer => .answer answer
    | none => .refuse

@[simp] theorem appended_fresh_answer_count_of_exact_append
    (initialHistory appended : List QueryRecord) :
    appendedFreshAnswerCount initialHistory (initialHistory ++ appended) =
      (freshAnswerEnumeration appended).length := by
  simp [appendedFreshAnswerCount]

/-- If `consumed` is exactly the fresh-answer enumeration of the chronological
suffix already appended, the reconstructed controller returns the next
projected scheduler answer. -/
theorem projected_fresh_controller_returns_next
    (initialHistory appended : List QueryRecord)
    (consumed remaining : List Digest256)
    (input : ShaInput) (answer : Digest256)
    (consumedExact : freshAnswerEnumeration appended = consumed) :
    controllerFromProjectedFreshAnswers initialHistory
        (consumed ++ answer :: remaining)
        (initialHistory ++ appended) input = .answer answer := by
  simp [controllerFromProjectedFreshAnswers,
    appendedFreshAnswerCount, consumedExact]

/-- The corresponding missing-query call is literally the ordinary
`queryOracle` fresh branch.  This theorem is local and causal: only the
already appended history and the next projected answer are inspected. -/
theorem query_oracle_with_projected_fresh_controller_exact
    (limits : OracleLimits) (actor : QueryActor)
    (state : OracleState) (initialHistory appended : List QueryRecord)
    (consumed remaining : List Digest256)
    (input : ShaInput) (answer : Digest256)
    (historyExact : state.history = initialHistory ++ appended)
    (consumedExact : freshAnswerEnumeration appended = consumed)
    (totalRoom : state.totalCalls < limits.totalCalls)
    (freshRoom : state.freshCalls < limits.freshCalls)
    (missing : lookupEntry state input = none) :
    queryOracle
      (controllerFromProjectedFreshAnswers initialHistory
        (consumed ++ answer :: remaining))
      limits actor state input =
        .ok (answer, freshQueryState actor state input answer) := by
  have controllerAnswer :
      controllerFromProjectedFreshAnswers initialHistory
          (consumed ++ answer :: remaining) state.history input =
        .answer answer := by
    rw [historyExact]
    exact projected_fresh_controller_returns_next initialHistory appended
      consumed remaining input answer consumedExact
  simp [queryOracle, Nat.not_le.mpr totalRoom, missing,
    Nat.not_le.mpr freshRoom, controllerAnswer, freshQueryState]

/-! ## Exact semantics of pausing before a fresh query -/

/-- Add a completed prefix length to the step counter of a machine run. -/
def addMachineRunSteps {Result : Type*}
    (run : MachineRun Result) (completed : Nat) : MachineRun Result :=
  { run with steps := run.steps + completed }

/-- Execute the residual represented by `seekNextFresh`.  Returned and abort
results already contain their exact cached-prefix step count.  At a request,
the controller is consulted exactly once and execution resumes from the
recorded continuation. -/
def resumeSeekNextFresh {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) :
    SeekNextFreshResult Result limits → MachineRun Result
  | .returned result state steps =>
      { halt := .returned result, oracle := state, steps := steps }
  | .explicitAbort reason state steps =>
      { halt := .oracleAbort reason, oracle := state, steps := steps }
  | .resourceAbort reason state steps =>
      { halt := .oracleAbort reason, oracle := state, steps := steps }
  | .outOfFuel state steps =>
      { halt := .outOfFuel, oracle := state, steps := steps }
  | .request state input next remainingFuel steps _coherent totalRoom
      freshRoom missing =>
      match controller state.history input with
      | .refuse =>
          { halt := .oracleAbort .controllerRefused
            oracle := state
            steps := steps + 1 }
      | .answer output =>
          addMachineRunSteps
            (runMachine controller limits actor remainingFuel
              (freshQueryState actor state input output) (next output))
            (steps + 1)

@[simp] theorem resume_seek_next_fresh_add_completed_query
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor)
    (result : SeekNextFreshResult Result limits) :
    resumeSeekNextFresh controller limits actor result.addCompletedQuery =
      addMachineRunSteps
        (resumeSeekNextFresh controller limits actor result) 1 := by
  cases result with
  | returned result state steps =>
      simp [SeekNextFreshResult.addCompletedQuery, resumeSeekNextFresh,
        addMachineRunSteps, Nat.add_assoc]
  | explicitAbort reason state steps =>
      simp [SeekNextFreshResult.addCompletedQuery, resumeSeekNextFresh,
        addMachineRunSteps, Nat.add_assoc]
  | resourceAbort reason state steps =>
      simp [SeekNextFreshResult.addCompletedQuery, resumeSeekNextFresh,
        addMachineRunSteps, Nat.add_assoc]
  | outOfFuel state steps =>
      simp [SeekNextFreshResult.addCompletedQuery, resumeSeekNextFresh,
        addMachineRunSteps, Nat.add_assoc]
  | request state input next remainingFuel steps coherent totalRoom freshRoom
      missing =>
      simp only [SeekNextFreshResult.addCompletedQuery,
        resumeSeekNextFresh]
      cases controller state.history input <;>
        simp [addMachineRunSteps, Nat.add_assoc]

/-- `seekNextFresh` is an executable factorization of `runMachine`: it runs
the entire cached prefix and pauses only where `runMachine` would next consult
the controller.  No equality between controllers is assumed. -/
theorem run_machine_eq_resume_seek_next_fresh
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (coherent : HistoryTotalCoherent state) :
    runMachine controller limits actor fuel state program =
      resumeSeekNextFresh controller limits actor
        (seekNextFresh limits actor fuel state program coherent) := by
  induction fuel generalizing state program with
  | zero =>
      cases program with
      | pure result => rfl
      | abort reason => rfl
      | query input next => rfl
  | succ fuel ih =>
      cases program with
      | pure result => rfl
      | abort reason => rfl
      | query input next =>
          simp only [seekNextFresh]
          split
          next totalBlocked =>
            simp [runMachine, queryOracle, totalBlocked,
              resumeSeekNextFresh]
          next totalRoom =>
            split
            next entry found =>
              have nextCoherent :=
                cached_query_state_preserves_history_total_coherent actor
                  state input entry coherent
              have tail := ih (cachedQueryState actor state input entry)
                (next entry.output) nextCoherent
              rw [resume_seek_next_fresh_add_completed_query]
              simpa [runMachine, queryOracle, totalRoom, found,
                cachedQueryState, addMachineRunSteps] using
                  congrArg (fun run => addMachineRunSteps run 1) tail
            next missing =>
              split
              next freshBlocked =>
                simp [runMachine, queryOracle, totalRoom, missing,
                  freshBlocked, resumeSeekNextFresh]
              next freshRoom =>
                cases decision : controller state.history input <;>
                  simp [runMachine, queryOracle, totalRoom, missing,
                    freshRoom, decision, resumeSeekNextFresh,
                    addMachineRunSteps, freshQueryState]

/-! ## Offset fresh-history coherence -/

/-- The current state extends one fixed initial history and its appended
suffix contains exactly the already projected scheduler answers. -/
def ProjectedFreshSuffix (initialHistory : List QueryRecord)
    (consumed : List Digest256) (state : OracleState) : Prop :=
  ∃ appended : List QueryRecord,
    state.history = initialHistory ++ appended ∧
      freshAnswerEnumeration appended = consumed

theorem projected_fresh_suffix_initial (state : OracleState) :
    ProjectedFreshSuffix state.history [] state := by
  exact ⟨[], by simp, rfl⟩

theorem projected_fresh_suffix_cached
    (initialHistory : List QueryRecord) (consumed : List Digest256)
    (actor : QueryActor) (state : OracleState) (input : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (suffix : ProjectedFreshSuffix initialHistory consumed state) :
    ProjectedFreshSuffix initialHistory consumed
      (cachedQueryState actor state input entry) := by
  rcases suffix with ⟨appended, historyExact, consumedExact⟩
  let record : QueryRecord :=
    { input := input
      output := entry.output
      actor := actor
      origin := cachedOrigin entry.source }
  refine ⟨appended ++ [record], ?_, ?_⟩
  · simp [cachedQueryState, record, historyExact, List.append_assoc]
  · rw [fresh_answer_enumeration_append, consumedExact]
    cases sourceEq : entry.source <;>
      simp [record, cachedOrigin, freshAnswerEnumeration, sourceEq]

theorem projected_fresh_suffix_fresh
    (initialHistory : List QueryRecord) (consumed : List Digest256)
    (actor : QueryActor) (state : OracleState) (input : ShaInput)
    (answer : Digest256)
    (suffix : ProjectedFreshSuffix initialHistory consumed state) :
    ProjectedFreshSuffix initialHistory (consumed ++ [answer])
      (freshQueryState actor state input answer) := by
  rcases suffix with ⟨appended, historyExact, consumedExact⟩
  let record : QueryRecord :=
    { input := input
      output := answer
      actor := actor
      origin := .fresh }
  refine ⟨appended ++ [record], ?_, ?_⟩
  · simp [freshQueryState, record, historyExact, List.append_assoc]
  · rw [fresh_answer_enumeration_append, consumedExact]
    rfl

/-- State retained by any terminal or paused `seekNextFresh` result. -/
def seekNextFreshOracle {Result : Type*} {limits : OracleLimits} :
    SeekNextFreshResult Result limits → OracleState
  | .returned _result state _steps => state
  | .explicitAbort _reason state _steps => state
  | .resourceAbort _reason state _steps => state
  | .outOfFuel state _steps => state
  | .request state _input _next _remainingFuel _steps _coherent _totalRoom
      _freshRoom _missing => state

@[simp] theorem seek_next_fresh_oracle_add_completed_query
    {Result : Type*} {limits : OracleLimits}
    (result : SeekNextFreshResult Result limits) :
    seekNextFreshOracle result.addCompletedQuery = seekNextFreshOracle result := by
  cases result <;> rfl

/-- Cached-prefix seeking never consumes a projected fresh answer, regardless
of whether it returns, aborts, exhausts fuel, or pauses at a request. -/
theorem seek_next_fresh_oracle_preserves_projected_suffix
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (initialHistory : List QueryRecord) (consumed : List Digest256)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (coherent : HistoryTotalCoherent state)
    (suffix : ProjectedFreshSuffix initialHistory consumed state) :
    ProjectedFreshSuffix initialHistory consumed
      (seekNextFreshOracle
        (seekNextFresh limits actor fuel state program coherent)) := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> simpa [seekNextFresh, seekNextFreshOracle] using suffix
  | succ fuel ih =>
      cases program with
      | pure result =>
          simpa [seekNextFresh, seekNextFreshOracle] using suffix
      | abort reason =>
          simpa [seekNextFresh, seekNextFreshOracle] using suffix
      | query currentInput currentNext =>
          simp only [seekNextFresh]
          split
          next _ => simpa [seekNextFreshOracle] using suffix
          next _ =>
            split
            next entry found =>
              simp only [seek_next_fresh_oracle_add_completed_query]
              exact ih
                (cachedQueryState actor state currentInput entry)
                (currentNext entry.output)
                (cached_query_state_preserves_history_total_coherent actor
                  state currentInput entry coherent)
                (projected_fresh_suffix_cached initialHistory consumed actor
                  state currentInput entry suffix)
            next missing =>
              split <;> simpa [seekNextFreshOracle] using suffix

/-- Cached-prefix normalization never increments the fresh-answer counter. -/
theorem seek_next_fresh_oracle_fresh_calls_eq
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (coherent : HistoryTotalCoherent state) :
    (seekNextFreshOracle
      (seekNextFresh limits actor fuel state program coherent)).freshCalls =
        state.freshCalls := by
  induction fuel generalizing state program with
  | zero =>
      cases program <;> rfl
  | succ fuel ih =>
      cases program with
      | pure result => rfl
      | abort reason => rfl
      | query input next =>
          simp only [seekNextFresh]
          split
          next _ => rfl
          next _ =>
            split
            next entry found =>
              simp only [seek_next_fresh_oracle_add_completed_query]
              simpa [cachedQueryState] using
                ih (cachedQueryState actor state input entry)
                  (next entry.output)
                  (cached_query_state_preserves_history_total_coherent actor
                    state input entry coherent)
            next missing =>
              split <;> rfl

/-- Request specialization of cached-prefix preservation. -/
theorem seek_next_fresh_request_preserves_projected_suffix
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (initialHistory : List QueryRecord) (consumed : List Digest256)
    (fuel : Nat) (state requestState : OracleState)
    (program : OracleMachine Result) (input : ShaInput)
    (next : ShaOutput → OracleMachine Result)
    (remainingFuel steps : Nat)
    (coherent : HistoryTotalCoherent state)
    (requestCoherent : HistoryTotalCoherent requestState)
    (totalRoom : requestState.totalCalls < limits.totalCalls)
    (freshRoom : requestState.freshCalls < limits.freshCalls)
    (missing : lookupEntry requestState input = none)
    (suffix : ProjectedFreshSuffix initialHistory consumed state)
    (sought : seekNextFresh limits actor fuel state program coherent =
      .request requestState input next remainingFuel steps requestCoherent
        totalRoom freshRoom missing) :
    ProjectedFreshSuffix initialHistory consumed requestState := by
  have preserved := seek_next_fresh_oracle_preserves_projected_suffix
    limits actor initialHistory consumed fuel state program coherent suffix
  rw [sought] at preserved
  exact preserved

/-- At a state satisfying offset coherence, exhausting the projected list
forces the reconstructed controller to refuse. -/
theorem projected_fresh_controller_refuses_after_consumed
    (initialHistory : List QueryRecord) (consumed : List Digest256)
    (state : OracleState) (input : ShaInput)
    (suffix : ProjectedFreshSuffix initialHistory consumed state) :
    controllerFromProjectedFreshAnswers initialHistory consumed
      state.history input = .refuse := by
  rcases suffix with ⟨appended, historyExact, consumedExact⟩
  rw [historyExact]
  simp [controllerFromProjectedFreshAnswers, appendedFreshAnswerCount,
    consumedExact]

/-! ## A proof-producing projected-answer interpreter -/

/-- Execute one machine segment from a finite list containing only its fresh
lazy-oracle answers.  Cached calls are eliminated by `seekNextFresh`; an empty
list at a pending request produces the same controller-refusal halt as
`runMachine`. -/
def runProjectedFreshSegment {Result : Type*}
    (limits : OracleLimits) (actor : QueryActor) :
    (answers : List Digest256) → (fuel : Nat) →
    (state : OracleState) → (program : OracleMachine Result) →
    HistoryTotalCoherent state → MachineRun Result
  | answers, fuel, state, program, coherent =>
      match seekNextFresh limits actor fuel state program coherent with
      | .returned result finalState steps =>
          { halt := .returned result, oracle := finalState, steps := steps }
      | .explicitAbort reason finalState steps =>
          { halt := .oracleAbort reason, oracle := finalState, steps := steps }
      | .resourceAbort reason finalState steps =>
          { halt := .oracleAbort reason, oracle := finalState, steps := steps }
      | .outOfFuel finalState steps =>
          { halt := .outOfFuel, oracle := finalState, steps := steps }
      | .request requestState input next remainingFuel steps requestCoherent
          _totalRoom _freshRoom _missing =>
          match answers with
          | [] =>
              { halt := .oracleAbort .controllerRefused
                oracle := requestState
                steps := steps + 1 }
          | answer :: rest =>
              addMachineRunSteps
                (runProjectedFreshSegment limits actor rest remainingFuel
                  (freshQueryState actor requestState input answer)
                  (next answer)
                  (fresh_query_state_preserves_history_total_coherent actor
                    requestState input answer requestCoherent))
                (steps + 1)

/-- The projected-answer interpreter is exactly `runMachine` under the
controller reconstructed from those projected answers.  The induction is on
the actual remaining answer list; programmed fork coordinates never enter it.
-/
theorem run_projected_fresh_segment_eq_run_machine
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (initialHistory : List QueryRecord) (consumed answers : List Digest256)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (coherent : HistoryTotalCoherent state)
    (suffix : ProjectedFreshSuffix initialHistory consumed state) :
    runProjectedFreshSegment limits actor answers fuel state program coherent =
      runMachine
        (controllerFromProjectedFreshAnswers initialHistory
          (consumed ++ answers))
        limits actor fuel state program := by
  induction answers generalizing fuel state program consumed with
  | nil =>
      rw [run_machine_eq_resume_seek_next_fresh
        (controllerFromProjectedFreshAnswers initialHistory
          (consumed ++ [])) limits actor fuel state program coherent]
      rw [runProjectedFreshSegment]
      cases sought : seekNextFresh limits actor fuel state program coherent with
      | returned result finalState steps => rfl
      | explicitAbort reason finalState steps => rfl
      | resourceAbort reason finalState steps => rfl
      | outOfFuel finalState steps => rfl
      | request requestState input next remainingFuel steps requestCoherent
          totalRoom freshRoom missing =>
          have requestSuffix :=
            seek_next_fresh_request_preserves_projected_suffix limits actor
              initialHistory consumed fuel state requestState program input
              next remainingFuel steps coherent requestCoherent totalRoom
              freshRoom missing suffix sought
          have refuses := projected_fresh_controller_refuses_after_consumed
            initialHistory consumed requestState input requestSuffix
          simpa [resumeSeekNextFresh, refuses]
  | cons answer rest ih =>
      rw [run_machine_eq_resume_seek_next_fresh
        (controllerFromProjectedFreshAnswers initialHistory
          (consumed ++ (answer :: rest))) limits actor fuel state program
            coherent]
      rw [runProjectedFreshSegment]
      cases sought : seekNextFresh limits actor fuel state program coherent with
      | returned result finalState steps => rfl
      | explicitAbort reason finalState steps => rfl
      | resourceAbort reason finalState steps => rfl
      | outOfFuel finalState steps => rfl
      | request requestState input next remainingFuel steps requestCoherent
          totalRoom freshRoom missing =>
          have requestSuffix :=
            seek_next_fresh_request_preserves_projected_suffix limits actor
              initialHistory consumed fuel state requestState program input
              next remainingFuel steps coherent requestCoherent totalRoom
              freshRoom missing suffix sought
          rcases requestSuffix with
            ⟨requestAppended, requestHistory, requestConsumed⟩
          have answersNext := projected_fresh_controller_returns_next
            initialHistory requestAppended consumed rest input answer
              requestConsumed
          have controllerAnswer :
              controllerFromProjectedFreshAnswers initialHistory
                  (consumed ++ (answer :: rest)) requestState.history input =
                .answer answer := by
            rw [requestHistory]
            exact answersNext
          have freshSuffix := projected_fresh_suffix_fresh initialHistory
            consumed actor requestState input answer
              ⟨requestAppended, requestHistory, requestConsumed⟩
          have tail := ih
            (consumed := consumed ++ [answer])
            (fuel := remainingFuel)
            (state := freshQueryState actor requestState input answer)
            (program := next answer)
            (fresh_query_state_preserves_history_total_coherent actor
              requestState input answer requestCoherent)
            freshSuffix
          rw [resumeSeekNextFresh]
          rw [controllerAnswer]
          rw [List.append_assoc] at tail
          exact congrArg
            (fun run => addMachineRunSteps run (steps + 1)) tail

/-! ## Exact returned-segment certificates -/

/-- A finite, operational certificate that one machine segment normally
returns after consuming exactly the listed fresh answers.  Each constructor
contains a literal `seekNextFresh` equation.  Cached queries are summarized
only by the step count already computed by that executable normalizer. -/
inductive ProjectedFreshReturnedTrace
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor) :
    (fuel : Nat) → (state : OracleState) →
    (program : OracleMachine Result) →
    (freshQueries : List (ShaInput × Digest256)) → (result : Result) →
    (finalState : OracleState) → (steps : Nat) → Prop where
  | returned
      (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
      (coherent : HistoryTotalCoherent state)
      (result : Result) (finalState : OracleState) (steps : Nat)
      (sought : seekNextFresh limits actor fuel state program coherent =
        .returned result finalState steps) :
      ProjectedFreshReturnedTrace limits actor fuel state program [] result
        finalState steps
  | fresh
      (fuel : Nat) (state requestState : OracleState)
      (program : OracleMachine Result)
      (coherent : HistoryTotalCoherent state)
      (input : ShaInput) (next : ShaOutput → OracleMachine Result)
      (remainingFuel cachedSteps : Nat)
      (requestCoherent : HistoryTotalCoherent requestState)
      (totalRoom : requestState.totalCalls < limits.totalCalls)
      (freshRoom : requestState.freshCalls < limits.freshCalls)
      (missing : lookupEntry requestState input = none)
      (sought : seekNextFresh limits actor fuel state program coherent =
        .request requestState input next remainingFuel cachedSteps
          requestCoherent totalRoom freshRoom missing)
      (answer : Digest256) (rest : List (ShaInput × Digest256))
      (result : Result) (finalState : OracleState) (tailSteps : Nat)
      (tail : ProjectedFreshReturnedTrace limits actor remainingFuel
        (freshQueryState actor requestState input answer) (next answer)
        rest
        result finalState tailSteps) :
      ProjectedFreshReturnedTrace limits actor fuel state program
        ((input, answer) :: rest) result finalState
        (tailSteps + (cachedSteps + 1))

/-- The operational trace certificate evaluates to its stated normal return
under the projected-answer interpreter. -/
theorem projected_fresh_returned_trace_interpreter_exact
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (freshQueries : List (ShaInput × Digest256)) (result : Result)
    (finalState : OracleState) (steps : Nat)
    (coherent : HistoryTotalCoherent state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) :
    runProjectedFreshSegment limits actor (freshQueries.map Prod.snd)
        fuel state program coherent =
      { halt := .returned result, oracle := finalState, steps := steps } := by
  induction trace with
  | returned fuel state program traceCoherent result finalState steps sought =>
      rw [runProjectedFreshSegment, sought]
  | fresh fuel state requestState program traceCoherent input next
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought answer rest result finalState tailSteps tail ih =>
      rw [runProjectedFreshSegment, sought]
      change addMachineRunSteps
          (runProjectedFreshSegment limits actor (rest.map Prod.snd)
            remainingFuel (freshQueryState actor requestState input answer)
            (next answer)
            (fresh_query_state_preserves_history_total_coherent actor
              requestState input answer requestCoherent))
          (cachedSteps + 1) =
        { halt := .returned result
          oracle := finalState
          steps := tailSteps + (cachedSteps + 1) }
      rw [ih]
      rfl

/-- A returned trace increments the fresh-answer counter by exactly the
number of projected machine-fresh answers it contains. -/
theorem projected_fresh_returned_trace_fresh_calls_exact
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (freshQueries : List (ShaInput × Digest256)) (result : Result)
    (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) :
    finalState.freshCalls = state.freshCalls + freshQueries.length := by
  induction trace with
  | returned fuel state program coherent result finalState steps sought =>
      have preserved := seek_next_fresh_oracle_fresh_calls_eq limits actor
        fuel state program coherent
      rw [sought] at preserved
      simpa only [seekNextFreshOracle, List.length_nil, Nat.add_zero] using
        preserved
  | fresh fuel state requestState program coherent input next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom missing sought answer rest
      result finalState tailSteps tail ih =>
      have prefixFresh := seek_next_fresh_oracle_fresh_calls_eq limits actor fuel
        state program coherent
      rw [sought] at prefixFresh
      have prefixFreshExact :
          requestState.freshCalls = state.freshCalls := by
        simpa only [seekNextFreshOracle] using prefixFresh
      rw [ih]
      change requestState.freshCalls + 1 + rest.length =
        state.freshCalls + ((input, answer) :: rest).length
      rw [prefixFreshExact]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Every projected fresh answer is one completed machine step.  Cached steps
can only increase the total. -/
theorem projected_fresh_returned_trace_answer_count_le_steps
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (freshQueries : List (ShaInput × Digest256)) (result : Result)
    (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) :
    freshQueries.length ≤ steps := by
  induction trace with
  | returned => simp
  | fresh fuel state requestState program coherent input next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom missing sought answer rest
      result finalState tailSteps tail ih =>
      simp only [List.length_cons]
      omega

/-- Exact projected content is preserved all the way to the normally returned
state. -/
theorem projected_fresh_returned_trace_preserves_suffix
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (initialHistory : List QueryRecord) (consumed : List Digest256)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (freshQueries : List (ShaInput × Digest256)) (result : Result)
    (finalState : OracleState) (steps : Nat)
    (suffix : ProjectedFreshSuffix initialHistory consumed state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) :
    ProjectedFreshSuffix initialHistory
      (consumed ++ freshQueries.map Prod.snd) finalState := by
  induction trace generalizing consumed with
  | returned fuel state program coherent result finalState steps sought =>
      have preserved := seek_next_fresh_oracle_preserves_projected_suffix
        limits actor initialHistory consumed fuel state program coherent suffix
      rw [sought] at preserved
      simpa only [seekNextFreshOracle, List.map_nil, List.append_nil] using
        preserved
  | fresh fuel state requestState program coherent input next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom missing sought answer rest
      result finalState tailSteps tail ih =>
      have requestSuffix :=
        seek_next_fresh_request_preserves_projected_suffix limits actor
          initialHistory consumed fuel state requestState program input next
          remainingFuel cachedSteps coherent requestCoherent totalRoom freshRoom
          missing suffix sought
      have afterAnswer := projected_fresh_suffix_fresh initialHistory consumed
        actor requestState input answer requestSuffix
      have finalSuffix := ih (consumed := consumed ++ [answer]) afterAnswer
      simpa [List.append_assoc] using finalSuffix

/-- Complete `runMachine` certificate reconstructed from the exact projected
fresh trace.  The only controller is the concrete projected controller; no
controller equality or returned-run premise is accepted. -/
theorem projected_fresh_returned_trace_run_machine_exact
    {Result : Type*} (limits : OracleLimits) (actor : QueryActor)
    (initialHistory : List QueryRecord) (consumed : List Digest256)
    (freshQueries : List (ShaInput × Digest256))
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (result : Result) (finalState : OracleState) (steps : Nat)
    (coherent : HistoryTotalCoherent state)
    (suffix : ProjectedFreshSuffix initialHistory consumed state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) :
    runMachine
        (controllerFromProjectedFreshAnswers initialHistory
          (consumed ++ freshQueries.map Prod.snd))
        limits actor fuel state program =
      { halt := .returned result, oracle := finalState, steps := steps } := by
  rw [← run_projected_fresh_segment_eq_run_machine limits actor initialHistory
    consumed (freshQueries.map Prod.snd) fuel state program coherent suffix]
  exact projected_fresh_returned_trace_interpreter_exact limits actor fuel
    state program freshQueries result finalState steps coherent trace

#print axioms machine_fresh_answers_append
#print axioms projected_fresh_controller_returns_next
#print axioms query_oracle_with_projected_fresh_controller_exact
#print axioms run_machine_eq_resume_seek_next_fresh
#print axioms seek_next_fresh_request_preserves_projected_suffix
#print axioms run_projected_fresh_segment_eq_run_machine
#print axioms projected_fresh_returned_trace_run_machine_exact
#print axioms projected_fresh_returned_trace_fresh_calls_exact
#print axioms projected_fresh_returned_trace_preserves_suffix

end

end AspisK1.V7Tag73ProjectedFreshController
