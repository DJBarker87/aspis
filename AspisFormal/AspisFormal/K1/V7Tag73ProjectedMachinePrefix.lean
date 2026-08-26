import AspisFormal.K1.V7Tag73TotalizedMachineReflection

/-!
# Consume one scheduler machine's projected fresh-answer prefix

The unified master tape contains both machine-fresh answers and programmed
fork coordinates.  This interpreter is used only at a machine node: it
consumes the shortest prefix of a supplied projected-answer list needed for
that machine to halt, and leaves the remainder for later phases.  Every
normal return carries the existing `ProjectedFreshReturnedTrace` built from
literal `seekNextFresh` equations.

This is the segment primitive needed to factor the global scheduler run.  It
does not accept a controller or a run equation.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ProjectedMachinePrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SchedulerNativeResult

noncomputable section

universe u

inductive ProjectedMachinePrefixFailure where
  | exposureExhausted
  | explicitAbort (reason : OracleAbort)
  | resourceAbort (reason : OracleAbort)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Dependent normal-return data for one machine segment.  `availableExact`
states that `freshQueries` consumed the literal shortest prefix and
`remaining` is the untouched suffix. -/
structure ProjectedMachinePrefixReturned
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (available : List Digest256) where
  result : Result
  finalState : OracleState
  finalCoherent : HistoryTotalCoherent finalState
  steps : Nat
  freshQueries : List (ShaInput × Digest256)
  remaining : List Digest256
  availableExact :
    available = freshQueries.map Prod.snd ++ remaining
  trace : ProjectedFreshReturnedTrace limits actor fuel state program
    freshQueries result finalState steps

abbrev ProjectedMachinePrefixResult
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (available : List Digest256) :=
  Except ProjectedMachinePrefixFailure
    (ProjectedMachinePrefixReturned limits actor fuel state program available)

/-- Internal certified form of the prefix interpreter.  The scheduler already
packages `seekNextFresh` with its state-coherence theorem; taking that package
explicitly lets downstream scheduler proofs case-split on one shared object
instead of rewriting through two proof-dependent matches.  `certifiedExact`
prevents callers from substituting an unrelated normalizer result. -/
def consumeCertifiedProjectedMachinePrefix
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor) :
    (available : List Digest256) → (fuel : Nat) →
    (state : OracleState) → (program : OracleMachine Result) →
    (coherent : HistoryTotalCoherent state) →
    (certified : CoherentSeekResult Result limits) →
    (certifiedExact :
      seekNextFresh limits actor fuel state program coherent =
        certified.value) →
      ProjectedMachinePrefixResult limits actor fuel state program available
  | available, fuel, state, program, coherent, certified, certifiedExact =>
      match sought : certified.value with
      | .returned result finalState steps =>
          .ok
            { result := result
              finalState := finalState
              finalCoherent :=
                seek_next_fresh_returned_state_coherent limits actor fuel state
                  finalState program coherent result steps
                  (certifiedExact.trans sought)
              steps := steps
              freshQueries := []
              remaining := available
              availableExact := by simp
              trace := .returned fuel state program coherent result finalState
                steps (certifiedExact.trans sought) }
      | .explicitAbort reason _finalState _steps =>
          .error (.explicitAbort reason)
      | .resourceAbort reason _finalState _steps =>
          .error (.resourceAbort reason)
      | .outOfFuel _finalState _steps =>
          .error .outOfFuel
      | .request requestState input next remainingFuel cachedSteps
          requestCoherent totalRoom freshRoom missing =>
          match available with
          | [] => .error .exposureExhausted
          | answer :: rest =>
              match consumeCertifiedProjectedMachinePrefix limits actor rest
                  remainingFuel
                  (freshQueryState actor requestState input answer)
                  (next answer)
                  (fresh_query_state_preserves_history_total_coherent actor
                    requestState input answer requestCoherent)
                  (certifiedSeekNextFresh limits actor remainingFuel
                    (freshQueryState actor requestState input answer)
                    (next answer)
                    (fresh_query_state_preserves_history_total_coherent actor
                      requestState input answer requestCoherent)) rfl with
              | .error reason => .error reason
              | .ok tail =>
                  .ok
                    { result := tail.result
                      finalState := tail.finalState
                      finalCoherent := tail.finalCoherent
                      steps := tail.steps + (cachedSteps + 1)
                      freshQueries := (input, answer) :: tail.freshQueries
                      remaining := tail.remaining
                      availableExact := by
                        simp only [List.map_cons, List.cons_append]
                        exact congrArg (List.cons answer) tail.availableExact
                      trace := .fresh fuel state requestState program coherent
                        input next remainingFuel cachedSteps requestCoherent
                        totalRoom freshRoom missing
                        (certifiedExact.trans sought) answer
                        tail.freshQueries tail.result tail.finalState tail.steps
                        tail.trace }

/-- Execute cached calls at once and consume one supplied answer only at an
actual missing query.  Recursion is on `available`, so the function is total
even when the oracle program itself is adversarial. -/
def consumeProjectedMachinePrefix
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (available : List Digest256) (fuel : Nat)
    (state : OracleState) (program : OracleMachine Result)
    (coherent : HistoryTotalCoherent state) :
      ProjectedMachinePrefixResult limits actor fuel state program available :=
  consumeCertifiedProjectedMachinePrefix limits actor available fuel state
    program coherent
    (certifiedSeekNextFresh limits actor fuel state program coherent) rfl

/-- The certificate constructs the ordinary machine run under the controller
derived from exactly the consumed projected answers.  Later answers and fork
coordinates cannot influence this equation. -/
theorem projected_machine_prefix_returned_run_exact
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available)
    (coherent : HistoryTotalCoherent state) :
    runMachine
        (controllerFromProjectedFreshAnswers state.history
          (returned.freshQueries.map Prod.snd))
        limits actor fuel state program =
      { halt := .returned returned.result
        oracle := returned.finalState
        steps := returned.steps } := by
  simpa using projected_fresh_returned_trace_run_machine_exact limits actor
    state.history [] returned.freshQueries fuel state program returned.result
    returned.finalState returned.steps coherent
    (projected_fresh_suffix_initial state) returned.trace

theorem projected_machine_prefix_consumption_exact
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (available : List Digest256) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) (coherent : HistoryTotalCoherent state)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available)
    (executed : consumeProjectedMachinePrefix limits actor available fuel state
      program coherent = .ok returned) :
    available = returned.freshQueries.map Prod.snd ++ returned.remaining := by
  exact returned.availableExact

/-- The consumed projected answers are exactly the fresh-origin enumeration
of the actual chronological history suffix stored in the returned oracle. -/
theorem projected_machine_prefix_fresh_answers_are_history_suffix
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    freshAnswerEnumeration (historySince state returned.finalState) =
      returned.freshQueries.map Prod.snd := by
  have suffix := projected_fresh_returned_trace_preserves_suffix limits actor
    state.history [] fuel state program returned.freshQueries returned.result
    returned.finalState returned.steps (projected_fresh_suffix_initial state)
    returned.trace
  rcases suffix with ⟨appended, historyExact, answersExact⟩
  unfold historySince
  rw [historyExact]
  simpa using answersExact

#print axioms projected_machine_prefix_returned_run_exact
#print axioms projected_machine_prefix_consumption_exact
#print axioms projected_machine_prefix_fresh_answers_are_history_suffix

end

end AspisK1.V7Tag73ProjectedMachinePrefix
