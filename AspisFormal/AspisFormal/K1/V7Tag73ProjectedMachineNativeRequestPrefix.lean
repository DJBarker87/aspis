import AspisFormal.K1.V7Tag73ActualNodeNativeEntryPrefix

/-!
# Exact native request at a projected Tag-73 machine prefix

The concrete restoration dispatcher receives a `ProjectedMachinePrefixReturned`
certificate for each prover and verifier callback.  Its flat list of fresh
queries is not, by itself, enough to identify the full pre-query `OracleState`
at a repeated `(input, answer)` coordinate.  This leaf consumes an *exact list
prefix* of that proof-relevant returned trace and proves that the executable
native scheduler exposes the corresponding machine request after precisely
those answers.

The construction is local and deterministic.  It assumes neither target
cleanliness nor a compiler conclusion; those are composed only after the
actual dispatcher has assembled the global chronological prefix.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerCausalStateAlignment

noncomputable section

universe u

/-- At an exact positional prefix of a proof-relevant returned machine trace,
the native scheduler exposes the literal indexed request state.  The entry
history prefix is retained for the later restored-node certificate. -/
theorem projected_fresh_trace_has_exact_native_request_at_prefix
    {globalOracleCalls : Nat} {Final MachineResult : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final) :
    ∀ {fuel : Nat} {entryState : OracleState}
      {program : OracleMachine MachineResult}
      {freshQueries : List (ShaInput × Digest256)}
      {result : MachineResult} {finalState : OracleState} {steps : Nat}
      (coherent : HistoryTotalCoherent entryState)
      (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
        freshQueries result finalState steps)
      (prior : List (ShaInput × Digest256)) (input : ShaInput)
      (answer : Digest256) (later : List (ShaInput × Digest256)),
      freshQueries = prior ++ (input, answer) :: later →
      ∃ requestState : OracleState,
        entryState.history <+: requestState.history ∧
          IsExactSchedulerNativeMachineFreshRequest actor requestState input
            (seekSchedulerNativeExposure transitionFuel
              (schedulerNativePrefixCursor transitionFuel
                (.machine limits limitBound actor entryState program fuel
                  coherent onReturned)
                (prior.map Prod.snd))) := by
  intro fuel entryState program freshQueries result finalState steps coherent
    trace
  induction trace with
  | returned fuel state program traceCoherent result finalState steps sought =>
      intro prior input answer later decomposition
      simp at decomposition
  | fresh fuel state requestState program traceCoherent headInput nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought headAnswer rest result finalState tailSteps tail ih =>
      intro prior input answer later decomposition
      have coherentExact : coherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      have stateToNext : state.history <+:
          (freshQueryState actor requestState headInput headAnswer).history := by
        have requestSuffix :=
          seek_next_fresh_request_preserves_projected_suffix limits actor
            state.history [] fuel state requestState program headInput
            nextProgram remainingFuel cachedSteps traceCoherent requestCoherent
            totalRoom freshRoom missing (projected_fresh_suffix_initial state)
            sought
        rcases requestSuffix with ⟨before, requestHistory, _answers⟩
        refine ⟨before ++ [{
          input := headInput
          output := headAnswer
          actor := actor
          origin := .fresh }], ?_⟩
        rw [freshQueryState]
        simp only [requestHistory, List.append_assoc]
      cases prior with
      | nil =>
          simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at decomposition
          rcases decomposition with
            ⟨⟨headInputExact, headAnswerExact⟩, restExact⟩
          subst input
          subst answer
          subst later
          cases transitionFuel with
          | zero => omega
          | succ current =>
              have requestPrefix : state.history <+: requestState.history := by
                have requestSuffix :=
                  seek_next_fresh_request_preserves_projected_suffix limits
                    actor state.history [] fuel state requestState program
                    headInput nextProgram remainingFuel cachedSteps
                    traceCoherent requestCoherent totalRoom freshRoom missing
                    (projected_fresh_suffix_initial state) sought
                rcases requestSuffix with ⟨before, requestHistory, _answers⟩
                exact ⟨before, requestHistory.symm⟩
              refine ⟨requestState, requestPrefix, ?_⟩
              simp only [List.map_nil, schedulerNativePrefixCursor]
              rw [seek_scheduler_native_exposure_machine_of_fresh current limits
                limitBound actor fuel state requestState program traceCoherent
                headInput nextProgram remainingFuel cachedSteps requestCoherent
                totalRoom freshRoom missing onReturned sought]
              exact .witness limits limitBound nextProgram remainingFuel
                requestCoherent totalRoom freshRoom missing onReturned
      | cons priorHead priorTail =>
          rcases priorHead with ⟨priorInput, priorAnswer⟩
          simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq] at decomposition
          rcases decomposition with
            ⟨⟨priorInputExact, priorAnswerExact⟩, tailExact⟩
          subst priorInput
          subst priorAnswer
          obtain ⟨laterRequestState, nextToRequest, nextExact⟩ :=
            ih
              (fresh_query_state_preserves_history_total_coherent actor
                requestState headInput headAnswer requestCoherent)
              priorTail input answer later tailExact
          refine ⟨laterRequestState, stateToNext.trans nextToRequest, ?_⟩
          cases transitionFuel with
          | zero => omega
          | succ current =>
              simp only [List.map_cons, schedulerNativePrefixCursor]
              rw [seek_scheduler_native_exposure_machine_of_fresh current limits
                limitBound actor fuel state requestState program traceCoherent
                headInput nextProgram remainingFuel cachedSteps requestCoherent
                totalRoom freshRoom missing onReturned sought]
              exact nextExact

/-- Structure-level dispatcher API.  A caller supplies only an exact
decomposition of the returned segment's own fresh-query list; the request
state and native cursor witness are constructed from its operational trace. -/
theorem projected_machine_prefix_has_exact_native_request_at_prefix
    {globalOracleCalls : Nat} {Final MachineResult : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (coherent : HistoryTotalCoherent entryState)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel entryState
      program available)
    (prior : List (ShaInput × Digest256)) (input : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition : returned.freshQueries =
      prior ++ (input, answer) :: later) :
    ∃ requestState : OracleState,
      entryState.history <+: requestState.history ∧
        IsExactSchedulerNativeMachineFreshRequest actor requestState input
          (seekSchedulerNativeExposure transitionFuel
            (schedulerNativePrefixCursor transitionFuel
              (.machine limits limitBound actor entryState program fuel coherent
                onReturned)
              (prior.map Prod.snd))) := by
  exact projected_fresh_trace_has_exact_native_request_at_prefix transitionFuel
    positive limits limitBound actor onReturned coherent returned.trace prior
      input answer later decomposition

/-- A positional decomposition of the projected *record* list uniquely lifts
to the underlying query/answer list.  This avoids a value-based membership
search when equal query pairs occur more than once. -/
theorem projected_machine_fresh_records_decomposition
    (actor : QueryActor) :
    ∀ (queries : List (ShaInput × Digest256))
      (priorRecords : List UnifiedExposureRecord)
      (input : ShaInput) (answer : Digest256)
      (laterRecords : List UnifiedExposureRecord),
      projectedMachineFreshRecords actor queries =
          priorRecords ++ .machineFresh actor input answer :: laterRecords →
      ∃ prior later : List (ShaInput × Digest256),
        queries = prior ++ (input, answer) :: later ∧
          priorRecords = projectedMachineFreshRecords actor prior ∧
          laterRecords = projectedMachineFreshRecords actor later := by
  intro queries
  induction queries with
  | nil =>
      intro priorRecords input answer laterRecords exact
      simp [projectedMachineFreshRecords] at exact
  | cons pair rest ih =>
      rcases pair with ⟨headInput, headAnswer⟩
      intro priorRecords input answer laterRecords exact
      cases priorRecords with
      | nil =>
          simp only [projectedMachineFreshRecords, List.nil_append,
            List.cons.injEq, UnifiedExposureRecord.machineFresh.injEq] at exact
          rcases exact with
            ⟨⟨_actorExact, headInputExact, headAnswerExact⟩, tailExact⟩
          subst input
          subst answer
          exact ⟨[], rest, rfl, rfl, tailExact.symm⟩
      | cons priorHead priorTail =>
          simp only [projectedMachineFreshRecords, List.cons_append,
            List.cons.injEq] at exact
          rcases exact with ⟨headExact, tailExact⟩
          subst priorHead
          obtain ⟨prior, later, queriesExact, priorExact, laterExact⟩ :=
            ih priorTail input answer laterRecords tailExact
          refine ⟨(headInput, headAnswer) :: prior, later, ?_, ?_, laterExact⟩
          · simpa only [List.cons_append] using
              congrArg (List.cons (headInput, headAnswer)) queriesExact
          · simpa only [projectedMachineFreshRecords] using
              congrArg
                (List.cons
                  (UnifiedExposureRecord.machineFresh actor headInput
                    headAnswer))
                priorExact

@[simp] theorem projected_machine_fresh_record_answers
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    (projectedMachineFreshRecords actor queries).map
        UnifiedExposureRecord.answer =
      queries.map Prod.snd := by
  induction queries with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, UnifiedExposureRecord.answer, ih]

/-- Dispatcher-facing form: its local chronology is stored as exposure
records, so the theorem performs the positional lift internally and returns
the exact native request after the record prefix's own answers. -/
theorem projected_machine_prefix_has_exact_native_request_at_record_prefix
    {globalOracleCalls : Nat} {Final MachineResult : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (coherent : HistoryTotalCoherent entryState)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel entryState
      program available)
    (priorRecords : List UnifiedExposureRecord)
    (input : ShaInput) (answer : Digest256)
    (laterRecords : List UnifiedExposureRecord)
    (decomposition : projectedMachineFreshRecords actor returned.freshQueries =
      priorRecords ++ .machineFresh actor input answer :: laterRecords) :
    ∃ requestState : OracleState,
      entryState.history <+: requestState.history ∧
        IsExactSchedulerNativeMachineFreshRequest actor requestState input
          (seekSchedulerNativeExposure transitionFuel
            (schedulerNativePrefixCursor transitionFuel
              (.machine limits limitBound actor entryState program fuel coherent
                onReturned)
              (priorRecords.map UnifiedExposureRecord.answer))) := by
  obtain ⟨prior, later, queriesExact, priorExact, laterExact⟩ :=
    projected_machine_fresh_records_decomposition actor returned.freshQueries
      priorRecords input answer laterRecords decomposition
  obtain ⟨requestState, historyPrefix, exactRequest⟩ :=
    projected_machine_prefix_has_exact_native_request_at_prefix transitionFuel
      positive limits limitBound actor fuel entryState program coherent
        onReturned available returned prior input answer later queriesExact
  refine ⟨requestState, historyPrefix, ?_⟩
  rw [priorExact]
  simpa only [projected_machine_fresh_record_answers] using exactRequest

#print axioms projected_fresh_trace_has_exact_native_request_at_prefix
#print axioms projected_machine_prefix_has_exact_native_request_at_prefix
#print axioms projected_machine_fresh_records_decomposition
#print axioms projected_machine_fresh_record_answers
#print axioms projected_machine_prefix_has_exact_native_request_at_record_prefix

end

end AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
