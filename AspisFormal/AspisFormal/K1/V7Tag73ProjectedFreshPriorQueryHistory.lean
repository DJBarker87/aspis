import AspisFormal.K1.V7Tag73CausalProgrammingFreshness
import AspisFormal.K1.V7Tag73SchedulerCausalStateAlignment

/-!
# Prior fresh queries are present at a projected request prefix

The source-facing q16 chronology proof needs more than a list position: if a
fresh coordinate occurs before a later state-producing coordinate in one
projected machine segment, the earlier query record must be present in the
later coordinate's cumulative pre-query history.  This file proves that fact
from the proof-relevant projected trace, without a value-based search.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ProjectedFreshPriorQueryHistory

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CausalProgrammingFreshness
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

def projectedFreshQueryRecord
    (actor : QueryActor) (query : ShaInput × Digest256) : QueryRecord :=
  { input := query.1
    output := query.2
    actor := actor
    origin := .fresh }

/-- Every projected fresh query remains present in the returned segment's
cumulative final history. -/
theorem projected_fresh_query_record_mem_final_history
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    {fuel : Nat} {entryState : OracleState}
    {program : OracleMachine MachineResult}
    {freshQueries : List (ShaInput × Digest256)}
    {result : MachineResult} {finalState : OracleState} {steps : Nat}
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps) :
    ∀ query ∈ freshQueries,
      projectedFreshQueryRecord actor query ∈ finalState.history := by
  induction trace with
  | returned =>
      intro query member
      simp at member
  | @fresh fuel state requestState program coherent input nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought answer rest result finalState tailSteps tail ih =>
      intro query member
      simp only [List.mem_cons] at member
      rcases member with queryExact | later
      · subst query
        have tailPrefix := projected_fresh_returned_trace_history_prefix
          limits actor remainingFuel
          (freshQueryState actor requestState input answer)
          (nextProgram answer) rest result finalState tailSteps tail
        apply tailPrefix.subset
        simp [projectedFreshQueryRecord, freshQueryState]
      · exact ih query later

/-- Every coordinate consumed by a positional projected-trace prefix is in
the cumulative history at the residual trace state.  Cached calls between
fresh coordinates are harmless because they only extend that history. -/
theorem projected_fresh_trace_suffix_prior_record_mem_history
    {MachineResult : Type u} {limits : OracleLimits} {actor : QueryActor}
    {result : MachineResult} {finalState : OracleState}
    {fuel : Nat} {state : OracleState}
    {program : OracleMachine MachineResult}
    {freshQueries : List (ShaInput × Digest256)} {steps : Nat}
    {trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps}
    {prior : List (ShaInput × Digest256)}
    {suffixFuel : Nat} {suffixState : OracleState}
    {suffixProgram : OracleMachine MachineResult}
    {suffixQueries : List (ShaInput × Digest256)} {suffixSteps : Nat}
    {suffixTrace : ProjectedFreshReturnedTrace limits actor suffixFuel
      suffixState suffixProgram suffixQueries result finalState suffixSteps}
    (relation : ProjectedFreshTraceSuffixAtPrefix limits actor trace prior
      suffixTrace) :
    ∀ query ∈ prior,
      projectedFreshQueryRecord actor query ∈ suffixState.history := by
  induction relation with
  | here =>
      intro query member
      simp at member
  | @next fuel state requestState program coherent input nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought answer rest tailSteps prior suffixFuel suffixState suffixProgram
      suffixQueries suffixSteps suffixTrace tail suffix ih =>
      intro query member
      simp only [List.mem_cons] at member
      rcases member with queryExact | later
      · subst query
        apply suffix.entry_history_prefix.subset
        simp [projectedFreshQueryRecord, freshQueryState]
      · exact ih query later

/-- Exact-prefix form: immediately before the selected fresh query, every
earlier projected fresh query is a literal record in the selected request
state's cumulative history. -/
theorem projected_fresh_query_at_exact_prefix_retains_prior_records
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    {fuel : Nat} {entryState : OracleState}
    {program : OracleMachine MachineResult}
    {freshQueries : List (ShaInput × Digest256)}
    {result : MachineResult} {finalState : OracleState} {steps : Nat}
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps)
    (prior : List (ShaInput × Digest256)) (input : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition : freshQueries = prior ++ (input, answer) :: later) :
    ∃ requestState : OracleState,
      (∀ query ∈ prior,
        projectedFreshQueryRecord actor query ∈ requestState.history) ∧
      lookupEntry requestState input = none := by
  obtain ⟨suffixFuel, suffixState, suffixProgram, suffixSteps, suffixTrace,
      suffixExact⟩ :=
    projected_fresh_trace_suffix_at_exact_prefix limits actor trace prior input
      answer later decomposition
  have priorAtSuffix :=
    projected_fresh_trace_suffix_prior_record_mem_history suffixExact
  cases suffixTrace
  case fresh =>
      rename_i requestState nextProgram remainingFuel cachedSteps
        requestCoherent totalRoom freshRoom tailSteps currentCoherent missing
        sought tail
      have requestSuffix :=
        seek_next_fresh_request_preserves_projected_suffix limits actor
          suffixState.history [] suffixFuel suffixState requestState
          suffixProgram input nextProgram remainingFuel cachedSteps
          currentCoherent requestCoherent totalRoom freshRoom missing
          (projected_fresh_suffix_initial suffixState) sought
      rcases requestSuffix with
        ⟨beforeRequest, requestHistory, _requestAnswers⟩
      have suffixToRequest : suffixState.history <+: requestState.history :=
        ⟨beforeRequest, requestHistory.symm⟩
      refine ⟨requestState, ?_, missing⟩
      intro query member
      exact suffixToRequest.subset (priorAtSuffix query member)

/-- Native operational form.  At a literal projected prefix, the exact
result-carrying scheduler request has a cumulative history containing every
fresh query in that prefix.  The indexed request state is shared by the
history and native-request conclusions, so no post-hoc state identification
is needed. -/
theorem projected_fresh_trace_has_native_request_with_prior_history
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
        (∀ query ∈ prior,
          projectedFreshQueryRecord actor query ∈ requestState.history) ∧
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
        refine ⟨before ++ [projectedFreshQueryRecord actor
          (headInput, headAnswer)], ?_⟩
        rw [freshQueryState]
        simp [projectedFreshQueryRecord, requestHistory, List.append_assoc]
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
                rcases requestSuffix with
                  ⟨before, requestHistory, _answers⟩
                exact ⟨before, requestHistory.symm⟩
              refine ⟨requestState, requestPrefix, ?_, ?_⟩
              · intro query member
                simp at member
              · simp only [List.map_nil, schedulerNativePrefixCursor]
                rw [seek_scheduler_native_exposure_machine_of_fresh current
                  limits limitBound actor fuel state requestState program
                  traceCoherent headInput nextProgram remainingFuel cachedSteps
                  requestCoherent totalRoom freshRoom missing onReturned sought]
                exact .witness limits limitBound nextProgram remainingFuel
                  requestCoherent totalRoom freshRoom missing onReturned
      | cons priorHead priorTail =>
          rcases priorHead with ⟨priorInput, priorAnswer⟩
          simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq] at decomposition
          rcases decomposition with
            ⟨⟨priorInputExact, priorAnswerExact⟩, tailExact⟩
          subst priorInput
          subst priorAnswer
          obtain ⟨laterRequestState, nextToRequest, priorTailAtRequest,
              nextExact⟩ :=
            ih
              (fresh_query_state_preserves_history_total_coherent actor
                requestState headInput headAnswer requestCoherent)
              priorTail input answer later tailExact
          refine ⟨laterRequestState, stateToNext.trans nextToRequest, ?_, ?_⟩
          · intro query member
            simp only [List.mem_cons] at member
            rcases member with queryExact | tailMember
            · subst query
              exact nextToRequest.subset (by
                simp [projectedFreshQueryRecord, freshQueryState])
            · exact priorTailAtRequest query tailMember
          · cases transitionFuel with
            | zero => omega
            | succ current =>
                simp only [List.map_cons, schedulerNativePrefixCursor]
                rw [seek_scheduler_native_exposure_machine_of_fresh current
                  limits limitBound actor fuel state requestState program
                  traceCoherent headInput nextProgram remainingFuel cachedSteps
                  requestCoherent totalRoom freshRoom missing onReturned sought]
                exact nextExact

#print axioms
  projected_fresh_trace_suffix_prior_record_mem_history
#print axioms projected_fresh_query_record_mem_final_history
#print axioms projected_fresh_query_at_exact_prefix_retains_prior_records
#print axioms projected_fresh_trace_has_native_request_with_prior_history

end

end AspisK1.V7Tag73ProjectedFreshPriorQueryHistory
