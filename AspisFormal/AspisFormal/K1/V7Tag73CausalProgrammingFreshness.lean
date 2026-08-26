import AspisFormal.K1.V7Tag73OperationalNodeCertificate
import AspisFormal.K1.V7Tag73ExactProbabilityCoverageAudit
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity
import AspisFormal.K1.V7Tag73OracleTableProvenance
import AspisFormal.K1.V7Tag73PrefixTableProvenance

/-!
# Chronological freshness of inherited Tag-73 programming records

This leaf discharges the programmed-table half of the concrete restoration
freshness problem.  For an actual causally-provenanced nonroot node, every
entry in its inherited programming ledger came from a scheduled fork whose
checkpoint state occurred earlier in the literal scheduler trace (or was the
public all-zero initial state).  A structurally fresh positive transition has
a checkpoint digest produced strictly later.  Seeded target cleanliness makes
those states distinct, and the deployed squeeze serialization then makes both
current pair inputs distinct from every inherited programmed input.

The theorem does not yet classify queried table entries.  That second half
uses the dependent operational target-clean certificate, which retains the
exact pre-query `OracleState.history`, together with the projected-machine
prefix alignment.  No lookup-freshness or compiler conclusion is assumed
here.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace AspisK1.V7Tag73CausalProgrammingFreshness

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerTargetClean
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73OracleTableProvenance
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73PrefixTableProvenance
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawStrictReplacementSuffix
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SqueezeInputStateInjectivity

noncomputable section

universe u

/-! ## Generic chronological list facts -/

theorem exists_append_cons_of_mem {α : Type*} (value : α) :
    ∀ {values : List α}, value ∈ values →
      ∃ before after, values = before ++ value :: after
  | [], member => by simp at member
  | head :: tail, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨[], tail, rfl⟩
      · obtain ⟨before, after, exact⟩ :=
          exists_append_cons_of_mem value member
        exact ⟨head :: before, after, by simp [exact]⟩

theorem accumulated_exposure_seen_contains_initial
    (initialSeen : Finset Digest256) :
    ∀ (records : List UnifiedExposureRecord) (answer : Digest256),
      answer ∈ initialSeen →
        answer ∈ accumulatedExposureSeen initialSeen records
  | [], answer, member => member
  | record :: records, answer, member => by
      apply accumulated_exposure_seen_contains_initial
        (extendUnifiedExposureSeen initialSeen record) records answer
      cases record <;> simp [extendUnifiedExposureSeen, member]

theorem active_exposure_answer_mem_accumulated_seen
    (initialSeen : Finset Digest256) (records : List UnifiedExposureRecord)
    (answer : Digest256) (active : ActiveExposureAnswer answer records) :
    answer ∈ accumulatedExposureSeen initialSeen records := by
  apply nonpadding_answer_mem_accumulated_exposure_seen
  rw [mem_nonpaddingExposureAnswers_iff]
  exact active

theorem active_exposure_answer_mem_accumulated_of_prefix
    (initialSeen : Finset Digest256)
    (earlier later : List UnifiedExposureRecord) (answer : Digest256)
    (prefixProof : earlier <+: later)
    (active : ActiveExposureAnswer answer earlier) :
    answer ∈ accumulatedExposureSeen initialSeen later := by
  rcases prefixProof with ⟨suffix, rfl⟩
  rw [accumulatedExposureSeen, List.foldl_append]
  exact accumulated_exposure_seen_contains_initial
    (accumulatedExposureSeen initialSeen earlier) suffix answer
      (active_exposure_answer_mem_accumulated_seen initialSeen earlier answer
        active)

/-- The earlier-pair prefix in the causal programming certificate cannot
reach into the final current pair: both scheduled pair lists have literal
length two.  Hence it is already a prefix of `traceBeforePair`. -/
theorem earlier_pair_before_is_prefix_of_current_trace_before
    (traceBefore : List UnifiedExposureRecord)
    (current earlier : ScheduledForkCoins)
    (earlierBefore earlierAfter : List UnifiedExposureRecord)
    (decomposition :
      traceBefore ++ scheduledPairRecords current =
        earlierBefore ++ scheduledPairRecords earlier ++ earlierAfter) :
    earlierBefore <+: traceBefore := by
  have wholePrefix : earlierBefore <+:
      traceBefore ++ scheduledPairRecords current := by
    rw [decomposition]
    simpa [List.append_assoc] using
      (List.prefix_append earlierBefore
        (scheduledPairRecords earlier ++ earlierAfter))
  have lengthEq := congrArg List.length decomposition
  have lengthLe : earlierBefore.length ≤ traceBefore.length := by
    simp [scheduledPairRecords] at lengthEq
    omega
  have takeExact := List.prefix_iff_eq_take.mp wholePrefix
  apply List.prefix_iff_eq_take.mpr
  calc
    earlierBefore =
        (traceBefore ++ scheduledPairRecords current).take
          earlierBefore.length := takeExact
    _ = traceBefore.take earlierBefore.length := by
      rw [List.take_append_of_le_length lengthLe]

/-! ## Eliminate a literal machine record from the dependent certificate -/

/-- Every machine-fresh record in the executable flat trace comes with the
actual pre-query oracle state retained by the dependent target-clean
certificate.  This is the non-circular bridge from a projected trace record
to the full cumulative history against which its answer was checked. -/
theorem operational_certificate_machine_record_has_causal_state
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    (certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape) :
    ∀ (actor : QueryActor) (input : ShaInput) (answer : Digest256),
      .machineFresh actor input answer ∈
          runUnifiedExposureTrace transitionFuel remaining cursor tape →
        ∃ (state : OracleState) (seenAt : Finset Digest256),
          answer ∉ operationalRequestTargets seenAt state.history input := by
  induction certificate with
  | done step seen seenBound cursor =>
      intro actor input answer member
      simp [runUnifiedExposureTrace] at member
  | halted step remaining seen seenBound cursor tape request tail ih =>
      intro actor input answer member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · exact ih actor input answer member
  | transitionLimit step remaining seen seenBound cursor tape request tail ih =>
      intro actor input answer member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · exact ih actor input answer member
  | @machineFresh MachineResult step remaining seen seenBound cursor tape
      limits limitBound queriedActor state queriedInput nextProgram
      remainingFuel coherent totalRoom freshRoom missing onReturned request
      answerAvoidsTargets tail ih =>
      intro actor input answer member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with current | later
      · cases current
        exact ⟨state, seen, answerAvoidsTargets⟩
      · exact ih actor input answer later
  | forkOutput step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template next request answerAvoidsTargets tail
      ih =>
      intro actor input answer member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with impossible | later
      · cases impossible
      · exact ih actor input answer later
  | forkAdvance step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template forkOutput next request
      answerAvoidsTargets tail ih =>
      intro actor input answer member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with impossible | later
      · cases impossible
      · exact ih actor input answer later

/-- The analogous eliminator for a scheduled advance coordinate retains the
actual frozen cumulative history against which that coin was checked. -/
theorem operational_certificate_fork_advance_has_causal_history
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    (certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape) :
    ∀ scheduled : ScheduledForkCoins,
      .forkAdvance scheduled ∈
          runUnifiedExposureTrace transitionFuel remaining cursor tape →
        ∃ seenAt : Finset Digest256,
          scheduled.forkAdvance ∉ operationalForkTargets seenAt
            scheduled.frozenHistory scheduled.outputInput
              scheduled.advanceInput := by
  induction certificate with
  | done step seen seenBound cursor =>
      intro scheduled member
      simp [runUnifiedExposureTrace] at member
  | halted step remaining seen seenBound cursor tape request tail ih =>
      intro scheduled member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with impossible | later
      · cases impossible
      · exact ih scheduled later
  | transitionLimit step remaining seen seenBound cursor tape request tail ih =>
      intro scheduled member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with impossible | later
      · cases impossible
      · exact ih scheduled later
  | machineFresh step remaining seen seenBound cursor tape limits limitBound
      actor state input nextProgram remainingFuel coherent totalRoom freshRoom
      missing onReturned request answerAvoidsTargets tail ih =>
      intro scheduled member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with impossible | later
      · cases impossible
      · exact ih scheduled later
  | forkOutput step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template next request answerAvoidsTargets tail
      ih =>
      intro scheduled member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with impossible | later
      · cases impossible
      · exact ih scheduled later
  | forkAdvance step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template forkOutput next request
      answerAvoidsTargets tail ih =>
      intro scheduled member
      simp only [runUnifiedExposureTrace, request, List.mem_cons] at member
      rcases member with current | later
      · cases current
        exact ⟨seen, answerAvoidsTargets⟩
      · exact ih scheduled later

/-- Both deployed squeeze inputs have the encoded state as their literal
32-byte prefix. -/
theorem literal_squeeze_input_has_state_prefix
    (state : Digest256) (domain : UInt8) :
    HasLiteralStatePrefix state (bytes state ++ [domain]) := by
  unfold HasLiteralStatePrefix
  rw [List.take_append_of_le_length]
  · simp
  · simp

/-! ## Cumulative histories inside one projected machine segment -/

/-- Every fresh query exposed by a returned projected machine segment is made
from a state whose cumulative history extends the segment-entry history.  The
statement retains the literal pre-query state and the executable missing-entry
fact; it does not identify that state with a caller-selected oracle state. -/
theorem projected_fresh_query_has_cumulative_request_state
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256))
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps) :
    ∀ input answer, (input, answer) ∈ freshQueries →
      ∃ requestState : OracleState,
        entryState.history <+: requestState.history ∧
          lookupEntry requestState input = none := by
  induction trace with
  | returned fuel state program coherent result finalState steps sought =>
      intro input answer member
      simp at member
  | fresh fuel state requestState program coherent headInput next
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought headAnswer rest result finalState tailSteps tail ih =>
      intro input answer member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with head | later
      · rcases head with ⟨rfl, rfl⟩
        have requestSuffix :=
          seek_next_fresh_request_preserves_projected_suffix limits actor
            state.history [] fuel state requestState program input next
              remainingFuel cachedSteps coherent requestCoherent totalRoom
                freshRoom missing (projected_fresh_suffix_initial state) sought
        rcases requestSuffix with ⟨appended, historyExact, _answersExact⟩
        exact ⟨requestState, ⟨appended, historyExact.symm⟩, missing⟩
      · obtain ⟨laterRequest, tailPrefix, tailMissing⟩ :=
          ih input answer later
        have requestSuffix :=
          seek_next_fresh_request_preserves_projected_suffix limits actor
            state.history [] fuel state requestState program headInput next
              remainingFuel cachedSteps coherent requestCoherent totalRoom
                freshRoom missing (projected_fresh_suffix_initial state) sought
        rcases requestSuffix with ⟨appended, historyExact, _answersExact⟩
        have entryToRequest : state.history <+: requestState.history :=
          ⟨appended, historyExact.symm⟩
        have requestToFresh : requestState.history <+:
            (freshQueryState actor requestState headInput headAnswer).history := by
          refine ⟨[{
            input := headInput
            output := headAnswer
            actor := actor
            origin := .fresh }], ?_⟩
          rfl
        exact ⟨laterRequest,
          entryToRequest.trans (requestToFresh.trans tailPrefix), tailMissing⟩

/-!
Membership alone is insufficient to identify a request state when equal query
pairs occur more than once.  The following proof-relevant relation consumes an
exact chronological prefix of the returned trace and retains the literal
suffix trace.  It is the positional bridge used by the native scheduler
factorization.
-/

/-- `suffixTrace` is obtained from `trace` by consuming exactly `prior` fresh
query/answer coordinates.  No search by value is involved. -/
inductive ProjectedFreshTraceSuffixAtPrefix
    {MachineResult : Type u} (limits : OracleLimits) (actor : QueryActor)
    {result : MachineResult} {finalState : OracleState} :
    {fuel : Nat} → {state : OracleState} →
      {program : OracleMachine MachineResult} →
      {freshQueries : List (ShaInput × Digest256)} → {steps : Nat} →
      ProjectedFreshReturnedTrace limits actor fuel state program freshQueries
        result finalState steps →
      (prior : List (ShaInput × Digest256)) →
      {suffixFuel : Nat} → {suffixState : OracleState} →
      {suffixProgram : OracleMachine MachineResult} →
      {suffixQueries : List (ShaInput × Digest256)} → {suffixSteps : Nat} →
      ProjectedFreshReturnedTrace limits actor suffixFuel suffixState
        suffixProgram suffixQueries result finalState suffixSteps → Prop where
  | here
      {fuel state program freshQueries steps}
      (trace : ProjectedFreshReturnedTrace limits actor fuel state program
        freshQueries result finalState steps) :
      ProjectedFreshTraceSuffixAtPrefix limits actor trace [] trace
  | next
      {fuel state requestState program coherent input nextProgram remainingFuel
        cachedSteps requestCoherent totalRoom freshRoom missing sought answer rest
        tailSteps}
      {prior : List (ShaInput × Digest256)}
      {suffixFuel suffixState suffixProgram suffixQueries suffixSteps}
      {suffixTrace : ProjectedFreshReturnedTrace limits actor suffixFuel
        suffixState suffixProgram suffixQueries result finalState suffixSteps}
      (tail : ProjectedFreshReturnedTrace limits actor remainingFuel
        (freshQueryState actor requestState input answer) (nextProgram answer)
        rest result finalState tailSteps)
      (suffix : ProjectedFreshTraceSuffixAtPrefix limits actor tail prior
        suffixTrace) :
      ProjectedFreshTraceSuffixAtPrefix limits actor
        (.fresh fuel state requestState program coherent input nextProgram
          remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
          sought answer rest result finalState tailSteps tail)
        ((input, answer) :: prior) suffixTrace

/-- Consuming a positional fresh-coordinate prefix can only extend the
cumulative oracle history. -/
theorem ProjectedFreshTraceSuffixAtPrefix.entry_history_prefix
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
    state.history <+: suffixState.history := by
  induction relation with
  | here => exact List.prefix_rfl
  | @next fuel state requestState program coherent input nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought answer rest tailSteps prior suffixFuel suffixState suffixProgram
      suffixQueries suffixSteps suffixTrace tail suffix ih =>
      have requestSuffix :=
        seek_next_fresh_request_preserves_projected_suffix limits actor
          state.history [] fuel state requestState program input nextProgram
          remainingFuel cachedSteps coherent requestCoherent totalRoom freshRoom
          missing (projected_fresh_suffix_initial state) sought
      rcases requestSuffix with ⟨before, requestHistory, _answers⟩
      have headPrefix : state.history <+:
          (freshQueryState actor requestState input answer).history := by
        refine ⟨before ++ [{
          input := input
          output := answer
          actor := actor
          origin := .fresh }], ?_⟩
        rw [freshQueryState]
        simp only [requestHistory, List.append_assoc]
      exact headPrefix.trans ih

/-- Exact-list decomposition yields the positional suffix relation.  The
target starts with a distinguished coordinate, so the empty returned trace is
impossible and no default suffix is needed. -/
theorem projected_fresh_trace_suffix_at_exact_prefix
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    {fuel : Nat} {entryState : OracleState}
    {program : OracleMachine MachineResult}
    {freshQueries : List (ShaInput × Digest256)}
    {result : MachineResult} {finalState : OracleState} {steps : Nat}
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps) :
    ∀ (prior : List (ShaInput × Digest256)) (input : ShaInput)
      (answer : Digest256) (later : List (ShaInput × Digest256)),
      freshQueries = prior ++ (input, answer) :: later →
      ∃ (suffixFuel : Nat) (suffixState : OracleState)
        (suffixProgram : OracleMachine MachineResult) (suffixSteps : Nat)
        (suffixTrace : ProjectedFreshReturnedTrace limits actor suffixFuel
          suffixState suffixProgram ((input, answer) :: later) result finalState
          suffixSteps),
        ProjectedFreshTraceSuffixAtPrefix limits actor trace prior suffixTrace := by
  induction trace with
  | returned fuel state program coherent result finalState steps sought =>
      intro prior input answer later decomposition
      simp at decomposition
  | fresh fuel state requestState program coherent headInput nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought headAnswer rest result finalState tailSteps tail ih =>
      intro prior input answer later decomposition
      cases prior with
      | nil =>
          simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at decomposition
          rcases decomposition with
            ⟨⟨headInputExact, headAnswerExact⟩, restExact⟩
          subst input
          subst answer
          subst later
          exact ⟨fuel, state, program, tailSteps + (cachedSteps + 1),
            .fresh fuel state requestState program coherent headInput nextProgram
              remainingFuel cachedSteps requestCoherent totalRoom freshRoom
              missing sought headAnswer rest result finalState tailSteps tail,
            .here _⟩
      | cons priorHead priorTail =>
          simp only [List.cons_append, List.cons.injEq] at decomposition
          rcases decomposition with ⟨headExact, tailExact⟩
          subst priorHead
          obtain ⟨suffixFuel, suffixState, suffixProgram, suffixSteps,
              suffixTrace, suffixExact⟩ :=
            ih priorTail input answer later tailExact
          exact ⟨suffixFuel, suffixState, suffixProgram, suffixSteps, suffixTrace,
            @ProjectedFreshTraceSuffixAtPrefix.next MachineResult limits actor
              result finalState fuel state requestState program coherent
              headInput nextProgram remainingFuel cachedSteps requestCoherent
              totalRoom freshRoom missing sought headAnswer rest tailSteps
              priorTail suffixFuel suffixState suffixProgram
              ((input, answer) :: later) suffixSteps suffixTrace tail suffixExact⟩

/-- Positional accessor for the exact fresh request at `prior.length`.  It
returns the literal request equation and the exact cumulative pre-query state,
not merely some equal `(input,answer)` member elsewhere in the trace. -/
theorem projected_fresh_query_at_exact_prefix_has_request_state
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
    ∃ (currentFuel : Nat) (currentState : OracleState)
      (currentProgram : OracleMachine MachineResult) (requestState : OracleState)
      (nextProgram : Digest256 → OracleMachine MachineResult)
      (remainingFuel cachedSteps tailSteps : Nat)
      (currentCoherent : HistoryTotalCoherent currentState)
      (requestCoherent : HistoryTotalCoherent requestState)
      (totalRoom : requestState.totalCalls < limits.totalCalls)
      (freshRoom : requestState.freshCalls < limits.freshCalls)
      (missing : lookupEntry requestState input = none)
      (sought : seekNextFresh limits actor currentFuel currentState currentProgram
        currentCoherent =
          .request requestState input nextProgram remainingFuel cachedSteps
            requestCoherent totalRoom freshRoom missing),
      entryState.history <+: currentState.history ∧
        entryState.history <+: requestState.history ∧
        ProjectedFreshReturnedTrace limits actor remainingFuel
          (freshQueryState actor requestState input answer) (nextProgram answer)
          later result finalState tailSteps := by
  obtain ⟨suffixFuel, suffixState, suffixProgram, suffixSteps, suffixTrace,
      suffixExact⟩ :=
    projected_fresh_trace_suffix_at_exact_prefix limits actor trace prior input
      answer later decomposition
  have entryPrefix : entryState.history <+: suffixState.history :=
    suffixExact.entry_history_prefix
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
      have entryToRequest : entryState.history <+: requestState.history :=
        entryPrefix.trans ⟨beforeRequest, requestHistory.symm⟩
      refine ⟨suffixFuel, suffixState, suffixProgram, requestState, nextProgram,
        remainingFuel, cachedSteps, tailSteps, currentCoherent, requestCoherent,
        totalRoom, freshRoom, missing, sought, entryPrefix, entryToRequest, ?_⟩
      exact tail

/-- In particular, every query already present when a machine segment starts
is present at the pre-query state of each fresh coordinate later exposed by
that segment. -/
theorem projected_fresh_query_retains_entry_history_record
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256))
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps)
    (input : ShaInput) (answer : Digest256)
    (queryMember : (input, answer) ∈ freshQueries)
    (record : QueryRecord) (recordMember : record ∈ entryState.history) :
    ∃ requestState : OracleState,
      record ∈ requestState.history ∧
        lookupEntry requestState input = none := by
  obtain ⟨requestState, historyPrefix, missing⟩ :=
    projected_fresh_query_has_cumulative_request_state limits actor fuel
      entryState program freshQueries result finalState steps trace input answer
        queryMember
  exact ⟨requestState, historyPrefix.subset recordMember, missing⟩

theorem projected_fresh_returned_trace_history_prefix
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256))
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps) :
    entryState.history <+: finalState.history := by
  have suffix := projected_fresh_returned_trace_preserves_suffix limits actor
    entryState.history [] fuel entryState program freshQueries result finalState
      steps (projected_fresh_suffix_initial entryState) trace
  rcases suffix with ⟨appended, historyExact, _answersExact⟩
  exact ⟨appended, historyExact.symm⟩

theorem projected_fresh_returned_trace_entry_coherent
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256))
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps) :
    HistoryTotalCoherent entryState := by
  cases trace with
  | returned fuel state program coherent result finalState steps sought =>
      exact coherent
  | fresh fuel state requestState program coherent input next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom missing sought answer rest
      result finalState tailSteps tail =>
      exact coherent

/-- Machine execution, including projected fresh queries and cached queries,
does not alter the cumulative programming ledger. -/
theorem projected_fresh_returned_trace_preserves_programming_history
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256))
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps) :
    finalState.programmingHistory = entryState.programmingHistory := by
  have coherent := projected_fresh_returned_trace_entry_coherent limits actor
    fuel entryState program freshQueries result finalState steps trace
  have runExact := projected_fresh_returned_trace_run_machine_exact limits actor
    entryState.history [] freshQueries fuel entryState program result finalState
      steps coherent (projected_fresh_suffix_initial entryState) trace
  simp only [List.nil_append] at runExact
  have preserved := run_machine_preserves_cumulative_programming_history
    (controllerFromProjectedFreshAnswers entryState.history
      (freshQueries.map Prod.snd)) limits actor fuel entryState program
  rw [runExact] at preserved
  exact preserved

theorem projected_fresh_returned_trace_preserves_table_coverage
    {MachineResult : Type u}
    (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (entryState : OracleState)
    (program : OracleMachine MachineResult)
    (freshQueries : List (ShaInput × Digest256))
    (result : MachineResult) (finalState : OracleState) (steps : Nat)
    (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
      freshQueries result finalState steps)
    (covered : TableCoveredByQueryOrProgramming entryState) :
    TableCoveredByQueryOrProgramming finalState := by
  have coherent := projected_fresh_returned_trace_entry_coherent limits actor
    fuel entryState program freshQueries result finalState steps trace
  have runExact := projected_fresh_returned_trace_run_machine_exact limits actor
    entryState.history [] freshQueries fuel entryState program result finalState
      steps coherent (projected_fresh_suffix_initial entryState) trace
  simp only [List.nil_append] at runExact
  have preserved := run_machine_preserves_table_covered_by_query_or_programming
    (controllerFromProjectedFreshAnswers entryState.history
      (freshQueries.map Prod.snd)) limits actor fuel entryState program covered
  rw [runExact] at preserved
  exact preserved

/-! ## Pair absence across cumulative history boundaries -/

/-- Equality of the input/output projection is enough to transport absence of
two concrete inputs; actor and origin metadata are irrelevant to this fact. -/
theorem first_either_none_of_query_answer_trace_eq
    (outputInput advanceInput : ShaInput)
    (actual expected : List QueryRecord)
    (traceExact : queryAnswerTrace actual = queryAnswerTrace expected)
    (expectedNone :
      firstEitherInputOccurrence outputInput advanceInput expected = none) :
    firstEitherInputOccurrence outputInput advanceInput actual = none := by
  apply (first_either_input_occurrence_none_iff outputInput advanceInput
    actual).mpr
  intro record recordMember
  have projectedMember : (record.input, record.output) ∈
      queryAnswerTrace actual := by
    exact List.mem_map.mpr ⟨record, recordMember, rfl⟩
  rw [traceExact] at projectedMember
  rcases List.mem_map.mp projectedMember with
    ⟨expectedRecord, expectedMember, pairExact⟩
  have expectedFresh := (first_either_input_occurrence_none_iff outputInput
    advanceInput expected).mp expectedNone expectedRecord expectedMember
  have inputExact : expectedRecord.input = record.input := by
    exact congrArg Prod.fst pairExact
  exact ⟨fun equal => expectedFresh.1 (inputExact.trans equal),
    fun equal => expectedFresh.2 (inputExact.trans equal)⟩

/-- If the cumulative entry history and the chronological segment suffix both
avoid a pair, their exact concatenation avoids it as well. -/
theorem first_either_none_of_entry_and_history_since
    (outputInput advanceInput : ShaInput)
    (entryState finalState : OracleState)
    (historyPrefix : entryState.history <+: finalState.history)
    (entryNone : firstEitherInputOccurrence outputInput advanceInput
      entryState.history = none)
    (suffixNone : firstEitherInputOccurrence outputInput advanceInput
      (historySince entryState finalState) = none) :
    firstEitherInputOccurrence outputInput advanceInput finalState.history =
      none := by
  apply (first_either_input_occurrence_none_iff outputInput advanceInput
    finalState.history).mpr
  intro record recordMember
  rw [history_eq_initial_append_history_since entryState finalState
    historyPrefix] at recordMember
  rcases List.mem_append.mp recordMember with entryMember | suffixMember
  · exact (first_either_input_occurrence_none_iff outputInput advanceInput
      entryState.history).mp entryNone record entryMember
  · exact (first_either_input_occurrence_none_iff outputInput advanceInput
      (historySince entryState finalState)).mp suffixNone record suffixMember

/-! ## Exact dispatcher-to-certificate alignment boundary -/

/-- The smallest operational alignment fact still required from the actual
dispatcher induction.  It does not assert lookup freshness: it identifies a
machine record emitted by one concrete node with the dependent causal-tree
coordinate that generated it, retaining both the cumulative-history prefix
and the already-proved target avoidance at that coordinate.

This predicate is stated here only to name the proof target.  No theorem below
accepts it as a replacement for the actual dispatcher induction. -/
def NodeMachineRecordHasCausalState
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {fullTrace : List UnifiedExposureRecord}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : ProjectedRestorationNodeExecution (Final := Final)
      startProgram environment
      configuration fullTrace accumulator child) : Prop :=
  ∀ actor input answer,
    .machineFresh actor input answer ∈
        execution.proverRecords ++ execution.verifierRecords →
      ∃ (requestState : OracleState) (seenAt : Finset Digest256),
        child.proverEntryOracle.history <+: requestState.history ∧
          answer ∉ operationalRequestTargets seenAt requestState.history input

/-! ## Programmed states precede every structurally fresh positive state -/

theorem prior_programmed_input_state_ne_positive_transition_state
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {Result : Type*}
    {cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result}
    {masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : CausallyProvenancedRestorationNodeExecution (Final := Final)
      startProgram
      environment configuration
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) accumulator child)
    (facts : ExactCompilerWholeTraceCleanFacts parameters transitionFuel cursor
      masterTape)
    (record : ProgrammingRecord)
    (recordMember : record ∈ child.proverEntryOracle.programmingHistory)
    (transitionIndex : Nat) (transition : FutureFreeTransition)
    (positive : transitionIndex ≠ 0)
    (transitionExact :
      verifierTransitionAt? child transitionIndex = some transition) :
    ∀ earlier inputState earlierBefore earlierAfter,
      execution.base.traceBeforePair ++
          scheduledPairRecords execution.base.scheduled =
        earlierBefore ++ scheduledPairRecords earlier ++ earlierAfter →
      ScheduledPairPrograms earlier record →
      ScheduledPairInputState earlier inputState →
      (inputState = zeroDigest256 ∨
        ActiveExposureAnswer inputState earlierBefore) →
      inputState ≠ transition.before.core.digest := by
  intro earlier inputState earlierBefore earlierAfter decomposition
    _programs _inputs inputOrigin
  have earlierPrefix : earlierBefore <+:
      execution.base.traceBeforePair :=
    earlier_pair_before_is_prefix_of_current_trace_before
      execution.base.traceBeforePair execution.base.scheduled earlier
        earlierBefore earlierAfter decomposition
  have currentOrigin := execution.positiveTransitionDigestProvenance
    transitionIndex transition positive transitionExact
  rcases currentOrigin with currentIsAdvance | currentIsActive
  · have atAdvance :=
      chronologically_clean_fork_advance_coordinate_of_append
        {zeroDigest256}
        (execution.base.traceBeforePair ++
          [.forkOutput execution.base.scheduled.frozenHistory
            execution.base.scheduled.outputInput
            execution.base.scheduled.advanceInput
            execution.base.scheduled.template
            execution.base.scheduled.forkOutput])
        (execution.base.proverRecords ++ execution.base.verifierRecords ++
          execution.base.traceAfterVerifier)
        execution.base.scheduled (by
          simpa [execution.base.fullTraceExact, scheduledPairRecords,
            List.append_assoc] using facts.everyCoordinate)
    have earlierSeen : inputState ∈ accumulatedExposureSeen {zeroDigest256}
        (execution.base.traceBeforePair ++
          [.forkOutput execution.base.scheduled.frozenHistory
            execution.base.scheduled.outputInput
            execution.base.scheduled.advanceInput
            execution.base.scheduled.template
            execution.base.scheduled.forkOutput]) := by
      rcases inputOrigin with rfl | active
      · exact accumulated_exposure_seen_contains_initial {zeroDigest256} _
          zeroDigest256 (by simp)
      · apply active_exposure_answer_mem_accumulated_of_prefix
          {zeroDigest256} earlierBefore
        · exact earlierPrefix.trans (by
            simpa [List.append_assoc] using
              (List.prefix_append execution.base.traceBeforePair
                (scheduledPairRecords execution.base.scheduled ++ middleBefore)))
        · exact active
    intro equal
    apply atAdvance.1
    rw [currentIsAdvance] at equal
    rw [← equal]
    exact earlierSeen
  · rcases currentIsActive with ⟨currentRecord, currentMember,
        currentAnswer⟩
    have currentMachine : ∃ actor input answer,
        currentRecord = .machineFresh actor input answer := by
      rcases List.mem_append.mp currentMember with proverMember | verifierMember
      · obtain ⟨input, answer, exact⟩ :=
          execution.base.proverRecordsOnly currentRecord proverMember
        exact ⟨.extractorReplay, input, answer, exact⟩
      · obtain ⟨input, answer, exact⟩ :=
          execution.base.verifierRecordsOnly currentRecord verifierMember
        exact ⟨.verifier, input, answer, exact⟩
    obtain ⟨actor, input, answer, currentRecordExact⟩ := currentMachine
    subst currentRecord
    have answerExact : answer = transition.before.core.digest := currentAnswer
    subst answer
    obtain ⟨middleBefore, middleAfter, middleExact⟩ :=
      exists_append_cons_of_mem
        (UnifiedExposureRecord.machineFresh actor input
          transition.before.core.digest)
        currentMember
    have atCurrent := chronologically_clean_machine_coordinate_of_append
      {zeroDigest256}
      (execution.base.traceBeforePair ++
        scheduledPairRecords execution.base.scheduled ++ middleBefore)
      (middleAfter ++ execution.base.traceAfterVerifier)
      actor input transition.before.core.digest (by
        simpa [execution.base.fullTraceExact, middleExact,
          List.append_assoc] using facts.everyCoordinate)
    have earlierSeen : inputState ∈ accumulatedExposureSeen {zeroDigest256}
        (execution.base.traceBeforePair ++
          scheduledPairRecords execution.base.scheduled ++ middleBefore) := by
      rcases inputOrigin with rfl | active
      · exact accumulated_exposure_seen_contains_initial {zeroDigest256} _
          zeroDigest256 (by simp)
      · apply active_exposure_answer_mem_accumulated_of_prefix
          {zeroDigest256} earlierBefore
        · exact earlierPrefix.trans (by
            simpa [List.append_assoc] using
              (List.prefix_append execution.base.traceBeforePair
                (scheduledPairRecords execution.base.scheduled ++ middleBefore)))
        · exact active
    intro equal
    exact atCurrent.1 (equal ▸ earlierSeen)

/-- Every cumulative query already present at a node's prover entry avoids the
pair inputs of a structurally fresh positive transition.  The only cross-layer
input is `alignment`, the exact dispatcher/certificate state identification
named above; it is strictly weaker than lookup freshness and carries no
compiler conclusion. -/
theorem prior_query_record_avoids_positive_transition_pair_inputs
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {Result : Type*}
    {cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result}
    {masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : CausallyProvenancedRestorationNodeExecution (Final := Final)
      startProgram
      environment configuration
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) accumulator child)
    (facts : ExactCompilerWholeTraceCleanFacts parameters transitionFuel cursor
      masterTape)
    (alignment : NodeMachineRecordHasCausalState execution.base)
    (record : QueryRecord)
    (recordMember : record ∈ child.proverEntryOracle.history)
    (transitionIndex : Nat) (transition : FutureFreeTransition)
    (positive : transitionIndex ≠ 0)
    (transitionExact :
      verifierTransitionAt? child transitionIndex = some transition) :
    record.input ≠ bytes transition.before.core.digest ++ [domSqueeze] ∧
      record.input ≠ bytes transition.before.core.digest ++ [domAdvance] := by
  have currentOrigin := execution.positiveTransitionDigestProvenance
    transitionIndex transition positive transitionExact
  rcases currentOrigin with currentIsAdvance | currentIsActive
  · have installed := program_concrete_pair_ready_installs_exact_coordinates
      configuration.oracleLimits configuration.pairProgrammingOrder
        execution.base.prepared.programmingBase child.proverEntryOracle
          execution.base.prepared.outputInput
            execution.base.prepared.advanceInput
              execution.base.scheduled.forkOutput
                execution.base.scheduled.forkAdvance
                  execution.base.programmingExact
    have frozenMember : record ∈ execution.base.scheduled.frozenHistory := by
      rw [execution.base.scheduledFrozenHistoryExact,
        ← installed.historyUnchanged]
      exact recordMember
    have advanceMember : .forkAdvance execution.base.scheduled ∈
        exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
          masterTape := by
      have decomposed : .forkAdvance execution.base.scheduled ∈
          execution.base.traceBeforePair ++
            scheduledPairRecords execution.base.scheduled ++
              execution.base.proverRecords ++ execution.base.verifierRecords ++
                execution.base.traceAfterVerifier := by
        simp [scheduledPairRecords]
      have membershipExact := congrArg
        (fun records : List UnifiedExposureRecord =>
          (.forkAdvance execution.base.scheduled : UnifiedExposureRecord) ∈
            records)
        execution.base.fullTraceExact
      exact membershipExact.mpr decomposed
    obtain ⟨seenAt, advanceAvoids⟩ :=
      operational_certificate_fork_advance_has_causal_history
        facts.operationalCertificate execution.base.scheduled advanceMember
    have avoidsRecord :
        ¬ HasLiteralStatePrefix execution.base.scheduled.forkAdvance
          record.input := by
      intro literalPrefix
      apply advanceAvoids
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact (operational_target_hit_iff_mem seenAt
        execution.base.scheduled.frozenHistory
          execution.base.scheduled.forkAdvance).mp
            (.literalPrefix record frozenMember literalPrefix)
    constructor
    · intro equalInput
      apply avoidsRecord
      rw [equalInput, currentIsAdvance]
      exact literal_squeeze_input_has_state_prefix
        execution.base.scheduled.forkAdvance domSqueeze
    · intro equalInput
      apply avoidsRecord
      rw [equalInput, currentIsAdvance]
      exact literal_squeeze_input_has_state_prefix
        execution.base.scheduled.forkAdvance domAdvance
  · rcases currentIsActive with ⟨currentRecord, currentMember,
        currentAnswer⟩
    rcases List.mem_append.mp currentMember with
        proverMember | verifierMember
    · obtain ⟨input, answer, recordExact⟩ :=
        execution.base.proverRecordsOnly currentRecord proverMember
      subst currentRecord
      obtain ⟨requestState, seenAt, entryPrefix, answerAvoids⟩ :=
        alignment .extractorReplay input answer
          (List.mem_append_left _ proverMember)
      have recordAtRequest : record ∈ requestState.history :=
        entryPrefix.subset recordMember
      have avoidsRecord := machine_answer_avoids_every_history_literal_prefix
        seenAt requestState input answer answerAvoids record recordAtRequest
      constructor
      · intro equalInput
        apply avoidsRecord
        rw [equalInput, ← currentAnswer]
        exact literal_squeeze_input_has_state_prefix answer domSqueeze
      · intro equalInput
        apply avoidsRecord
        rw [equalInput, ← currentAnswer]
        exact literal_squeeze_input_has_state_prefix answer domAdvance
    · obtain ⟨input, answer, recordExact⟩ :=
        execution.base.verifierRecordsOnly currentRecord verifierMember
      subst currentRecord
      obtain ⟨requestState, seenAt, entryPrefix, answerAvoids⟩ :=
        alignment .verifier input answer
          (List.mem_append_right _ verifierMember)
      have recordAtRequest : record ∈ requestState.history :=
        entryPrefix.subset recordMember
      have avoidsRecord := machine_answer_avoids_every_history_literal_prefix
        seenAt requestState input answer answerAvoids record recordAtRequest
      constructor
      · intro equalInput
        apply avoidsRecord
        rw [equalInput, ← currentAnswer]
        exact literal_squeeze_input_has_state_prefix answer domSqueeze
      · intro equalInput
        apply avoidsRecord
        rw [equalInput, ← currentAnswer]
        exact literal_squeeze_input_has_state_prefix answer domAdvance

/-- List-level form of the preceding record theorem. -/
theorem positive_transition_pair_absent_from_prover_entry_history
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {Result : Type*}
    {cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result}
    {masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : CausallyProvenancedRestorationNodeExecution (Final := Final)
      startProgram
      environment configuration
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) accumulator child)
    (facts : ExactCompilerWholeTraceCleanFacts parameters transitionFuel cursor
      masterTape)
    (alignment : NodeMachineRecordHasCausalState execution.base)
    (transitionIndex : Nat) (transition : FutureFreeTransition)
    (positive : transitionIndex ≠ 0)
    (transitionExact :
      verifierTransitionAt? child transitionIndex = some transition) :
    firstEitherInputOccurrence
        (bytes transition.before.core.digest ++ [domSqueeze])
        (bytes transition.before.core.digest ++ [domAdvance])
        child.proverEntryOracle.history = none := by
  apply (first_either_input_occurrence_none_iff
    (bytes transition.before.core.digest ++ [domSqueeze])
    (bytes transition.before.core.digest ++ [domAdvance])
    child.proverEntryOracle.history).mpr
  intro record recordMember
  exact prior_query_record_avoids_positive_transition_pair_inputs execution
    facts alignment record recordMember transitionIndex transition positive
      transitionExact

/-- Prefix preparation for a structurally fresh positive child transition
cannot reintroduce either selected pair input into its query history.  The
proof follows the executable preparation branches.  In the absent-occurrence
branch it uses the complete returned prover segment; in the occurrence branch
it uses the literal prefix replay and the checked query-answer trace. -/
theorem ready_positive_child_programming_base_query_and_programming_provenance
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {Result : Type*}
    {cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result}
    {masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : CausallyProvenancedRestorationNodeExecution (Final := Final)
      startProgram
      environment configuration
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) accumulator child)
    (facts : ExactCompilerWholeTraceCleanFacts parameters transitionFuel cursor
      masterTape)
    (alignment : NodeMachineRecordHasCausalState execution.base)
    (entryCovered :
      TableCoveredByQueryOrProgramming child.proverEntryOracle)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (parentFound : accumulator.node? request.nodeId = some child)
    (positive : request.verifierTransitionIndex ≠ 0)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    firstEitherInputOccurrence prepared.outputInput prepared.advanceInput
        prepared.programmingBase.history = none ∧
      prepared.programmingBase.programmingHistory =
        child.proverEntryOracle.programmingHistory ∧
      TableCoveredByQueryOrProgramming prepared.programmingBase := by
  cases selectedTransition : verifierTransitionAt? child
      request.verifierTransitionIndex with
  | none =>
      simp [prepareConcreteRestorationFromStartProgram, parentFound,
        selectedTransition] at ready
  | some transition =>
      cases selectedPair : squeezePairInputsOfTransition transition with
      | none =>
          simp [prepareConcreteRestorationFromStartProgram, parentFound,
            selectedTransition, selectedPair] at ready
      | some pair =>
          rcases pair with ⟨outputInput, advanceInput⟩
          have pairInputs := squeeze_pair_inputs_exact_give_input_state
            transition outputInput advanceInput selectedPair
          have entryNone : firstEitherInputOccurrence outputInput advanceInput
              child.proverEntryOracle.history = none := by
            simpa [pairInputs.1, pairInputs.2] using
              positive_transition_pair_absent_from_prover_entry_history
                execution facts alignment request.verifierTransitionIndex
                  transition positive selectedTransition
          cases selectedOccurrence : firstEitherInputOccurrence outputInput
              advanceInput child.proverHistory with
          | none =>
              simp [prepareConcreteRestorationFromStartProgram, parentFound,
                selectedTransition, selectedPair, selectedOccurrence] at ready
              subst prepared
              have historyPrefix : child.proverEntryOracle.history <+:
                  child.proverFinalOracle.history := by
                rw [← execution.base.proverFinalExact]
                exact projected_fresh_returned_trace_history_prefix
                  configuration.oracleLimits .extractorReplay
                    configuration.proverReplayFuel child.proverEntryOracle
                      (schedulerStageProgram Final
                        (totalizeOracleMachine configuration.proverReplayFuel
                          startProgram))
                      execution.base.proverPrefix.freshQueries
                      execution.base.proverPrefix.result
                      execution.base.proverPrefix.finalState
                      execution.base.proverPrefix.steps
                      execution.base.proverPrefix.trace
              refine ⟨?_, ?_, ?_⟩
              · exact first_either_none_of_entry_and_history_since outputInput
                  advanceInput child.proverEntryOracle child.proverFinalOracle
                    historyPrefix entryNone (by
                      simpa [ConcreteRestorationNode.proverHistory] using
                        selectedOccurrence)
              · rw [← execution.base.proverFinalExact]
                exact
                  projected_fresh_returned_trace_preserves_programming_history
                    configuration.oracleLimits .extractorReplay
                      configuration.proverReplayFuel child.proverEntryOracle
                        (schedulerStageProgram Final
                          (totalizeOracleMachine
                            configuration.proverReplayFuel startProgram))
                        execution.base.proverPrefix.freshQueries
                        execution.base.proverPrefix.result
                        execution.base.proverPrefix.finalState
                        execution.base.proverPrefix.steps
                        execution.base.proverPrefix.trace
              · rw [← execution.base.proverFinalExact]
                exact projected_fresh_returned_trace_preserves_table_coverage
                  configuration.oracleLimits .extractorReplay
                    configuration.proverReplayFuel child.proverEntryOracle
                      (schedulerStageProgram Final
                        (totalizeOracleMachine configuration.proverReplayFuel
                          startProgram))
                      execution.base.proverPrefix.freshQueries
                      execution.base.proverPrefix.result
                      execution.base.proverPrefix.finalState
                      execution.base.proverPrefix.steps
                      execution.base.proverPrefix.trace entryCovered
          | some occurrence =>
              have occurrenceSpec := first_either_input_occurrence_spec
                outputInput advanceInput child.proverHistory occurrence
                  selectedOccurrence
              have beforeNone : firstEitherInputOccurrence outputInput
                  advanceInput occurrence.before = none := by
                apply (first_either_input_occurrence_none_iff outputInput
                  advanceInput occurrence.before).mpr
                exact occurrenceSpec.2.1
              let prefixRun := runPrefix
                (recordedPrefixController
                  child.proverEntryOracle.history.length occurrence.before)
                configuration.oracleLimits .extractorReplay
                occurrence.before.length child.proverEntryOracle startProgram
              cases halted : prefixRun.halt with
              | returned result =>
                  simp [prepareConcreteRestorationFromStartProgram,
                    parentFound, selectedTransition, selectedPair,
                    selectedOccurrence, prefixRun, halted] at ready
              | oracleAbort reason =>
                  simp [prepareConcreteRestorationFromStartProgram,
                    parentFound, selectedTransition, selectedPair,
                    selectedOccurrence, prefixRun, halted] at ready
              | paused residual =>
                  cases residual with
                  | pure result =>
                      simp [prepareConcreteRestorationFromStartProgram,
                        parentFound, selectedTransition, selectedPair,
                        selectedOccurrence, prefixRun, halted] at ready
                  | abort reason =>
                      simp [prepareConcreteRestorationFromStartProgram,
                        parentFound, selectedTransition, selectedPair,
                        selectedOccurrence, prefixRun, halted] at ready
                  | query pendingInput next =>
                      by_cases pendingMismatch :
                          pendingInput ≠ occurrence.chosen.input
                      · simp [prepareConcreteRestorationFromStartProgram,
                          parentFound, selectedTransition, selectedPair,
                          selectedOccurrence, prefixRun, halted,
                          pendingMismatch] at ready
                      · by_cases traceMismatch : queryAnswerTrace
                            (historySince child.proverEntryOracle
                              prefixRun.oracle) ≠
                            queryAnswerTrace occurrence.before
                        · simp [prepareConcreteRestorationFromStartProgram,
                            parentFound, selectedTransition, selectedPair,
                            selectedOccurrence, prefixRun, halted,
                            pendingMismatch, traceMismatch] at ready
                        · have traceExact : queryAnswerTrace
                              (historySince child.proverEntryOracle
                                prefixRun.oracle) =
                              queryAnswerTrace occurrence.before :=
                            not_ne_iff.mp traceMismatch
                          simp [prepareConcreteRestorationFromStartProgram,
                            parentFound, selectedTransition, selectedPair,
                            selectedOccurrence, prefixRun, halted,
                            pendingMismatch, traceMismatch] at ready
                          subst prepared
                          have suffixNone :=
                            first_either_none_of_query_answer_trace_eq
                              outputInput advanceInput
                                (historySince child.proverEntryOracle
                                  prefixRun.oracle)
                                occurrence.before traceExact beforeNone
                          refine ⟨?_, ?_, ?_⟩
                          · exact first_either_none_of_entry_and_history_since
                              outputInput advanceInput child.proverEntryOracle
                                prefixRun.oracle
                                (prefix_run_history_is_preserved
                                  (recordedPrefixController
                                    child.proverEntryOracle.history.length
                                    occurrence.before)
                                  configuration.oracleLimits .extractorReplay
                                  occurrence.before.length
                                  child.proverEntryOracle startProgram)
                                entryNone suffixNone
                          · exact run_prefix_preserves_programming_history
                              (recordedPrefixController
                                child.proverEntryOracle.history.length
                                occurrence.before)
                              configuration.oracleLimits .extractorReplay
                              occurrence.before.length child.proverEntryOracle
                              startProgram
                          · exact
                              run_prefix_preserves_table_covered_by_query_or_programming
                                (recordedPrefixController
                                  child.proverEntryOracle.history.length
                                  occurrence.before)
                                configuration.oracleLimits .extractorReplay
                                occurrence.before.length
                                child.proverEntryOracle startProgram entryCovered

/-- Query-absence projection of the exact preparation provenance theorem. -/
theorem ready_positive_child_programming_base_query_pair_absent
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {Result : Type*}
    {cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result}
    {masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : CausallyProvenancedRestorationNodeExecution (Final := Final)
      startProgram
      environment configuration
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) accumulator child)
    (facts : ExactCompilerWholeTraceCleanFacts parameters transitionFuel cursor
      masterTape)
    (alignment : NodeMachineRecordHasCausalState execution.base)
    (entryCovered :
      TableCoveredByQueryOrProgramming child.proverEntryOracle)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (parentFound : accumulator.node? request.nodeId = some child)
    (positive : request.verifierTransitionIndex ≠ 0)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    firstEitherInputOccurrence prepared.outputInput prepared.advanceInput
      prepared.programmingBase.history = none :=
  (ready_positive_child_programming_base_query_and_programming_provenance
    execution facts alignment entryCovered request prepared parentFound positive
      ready).1

/-- Therefore no inherited programming record can name either SHA input of a
structurally fresh positive squeeze transition. -/
theorem prior_programming_record_avoids_positive_transition_pair_inputs
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {Result : Type*}
    {cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result}
    {masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : CausallyProvenancedRestorationNodeExecution (Final := Final)
      startProgram
      environment configuration
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) accumulator child)
    (facts : ExactCompilerWholeTraceCleanFacts parameters transitionFuel cursor
      masterTape)
    (record : ProgrammingRecord)
    (recordMember : record ∈ child.proverEntryOracle.programmingHistory)
    (transitionIndex : Nat) (transition : FutureFreeTransition)
    (positive : transitionIndex ≠ 0)
    (transitionExact :
      verifierTransitionAt? child transitionIndex = some transition) :
    record.input ≠ bytes transition.before.core.digest ++ [domSqueeze] ∧
      record.input ≠ bytes transition.before.core.digest ++ [domAdvance] := by
  obtain ⟨earlier, earlierBefore, earlierAfter, inputState,
      decomposition, programs, inputs, inputOrigin⟩ :=
    execution.programmingHistoryHasEarlierPairProvenance record recordMember
  have stateNe := prior_programmed_input_state_ne_positive_transition_state
    execution facts record recordMember transitionIndex transition positive
      transitionExact earlier inputState earlierBefore earlierAfter
        decomposition programs inputs inputOrigin
  have earlierInput :
      record.input = bytes inputState ++ [domSqueeze] ∨
        record.input = bytes inputState ++ [domAdvance] := by
    rcases programs.2 with outputHalf | advanceHalf
    · exact Or.inl (outputHalf.1.trans inputs.1)
    · exact Or.inr (advanceHalf.1.trans inputs.2)
  constructor
  · intro overlap
    exact stateNe (pair_input_overlap_implies_state_eq
      transition.before.core.digest inputState
      (bytes transition.before.core.digest ++ [domSqueeze]) record.input
      (Or.inl rfl) earlierInput overlap)
  · intro overlap
    exact stateNe (pair_input_overlap_implies_state_eq
      transition.before.core.digest inputState
      (bytes transition.before.core.digest ++ [domAdvance]) record.input
      (Or.inr rfl) earlierInput overlap)

/-! ## Lookup elimination after the query case has been discharged -/

/-- Once actual causal-history analysis has excluded both current pair inputs
from the programming base's query history, table coverage reduces every
remaining lookup to an inherited programming record.  The preceding theorem
then eliminates that record.  The hypotheses are operational invariants
(coverage, literal query absence, and preservation of the programming ledger),
not lookup-freshness or a compiler conclusion. -/
theorem positive_transition_pair_lookups_none_of_query_absence
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {Result : Type*}
    {cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result}
    {masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : CausallyProvenancedRestorationNodeExecution (Final := Final)
      startProgram
      environment configuration
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) accumulator child)
    (facts : ExactCompilerWholeTraceCleanFacts parameters transitionFuel cursor
      masterTape)
    (state : OracleState)
    (covered : TableCoveredByQueryOrProgramming state)
    (programmingHistoryExact :
      state.programmingHistory = child.proverEntryOracle.programmingHistory)
    (transitionIndex : Nat) (transition : FutureFreeTransition)
    (positive : transitionIndex ≠ 0)
    (transitionExact :
      verifierTransitionAt? child transitionIndex = some transition)
    (outputInput advanceInput : ShaInput)
    (inputsExact :
      outputInput = bytes transition.before.core.digest ++ [domSqueeze] ∧
        advanceInput = bytes transition.before.core.digest ++ [domAdvance])
    (noPair : firstEitherInputOccurrence outputInput advanceInput
      state.history = none) :
    lookupEntry state outputInput = none ∧
      lookupEntry state advanceInput = none := by
  constructor
  · cases found : lookupEntry state outputInput with
    | none => rfl
    | some entry =>
        obtain ⟨record, recordMember, recordInput, _recordOutput⟩ :=
          no_pair_output_lookup_conflict_is_prior_programming state
            outputInput advanceInput entry covered noPair found
        have childMember :
            record ∈ child.proverEntryOracle.programmingHistory := by
          rw [← programmingHistoryExact]
          exact recordMember
        have avoids :=
          prior_programming_record_avoids_positive_transition_pair_inputs
            execution facts record childMember transitionIndex transition
              positive transitionExact
        exact (avoids.1 (recordInput.trans inputsExact.1)).elim
  · cases found : lookupEntry state advanceInput with
    | none => rfl
    | some entry =>
        obtain ⟨record, recordMember, recordInput, _recordOutput⟩ :=
          no_pair_advance_lookup_conflict_is_prior_programming state
            outputInput advanceInput entry covered noPair found
        have childMember :
            record ∈ child.proverEntryOracle.programmingHistory := by
          rw [← programmingHistoryExact]
          exact recordMember
        have avoids :=
          prior_programming_record_avoids_positive_transition_pair_inputs
            execution facts record childMember transitionIndex transition
              positive transitionExact
        exact (avoids.2 (recordInput.trans inputsExact.2)).elim

/-- Actual prepared-state specialization.  Once the synchronized dispatcher
induction supplies `alignment` and ordinary operational table coverage is
available, a positive child request has both pair inputs absent from its
literal programming base.  Neither absence is assumed. -/
theorem ready_positive_child_programming_base_pair_lookups_none
    {Statement Proof Payload Final : Type u}
    {startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)}
    {environment : FutureFreeEnvironment}
    {configuration : ConcreteRestorationConfiguration}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {Result : Type*}
    {cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result}
    {masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    {accumulator : ConcreteRestorationAccumulator Statement Proof Payload}
    {child : ConcreteRestorationNode Statement Proof Payload}
    (execution : CausallyProvenancedRestorationNodeExecution (Final := Final)
      startProgram
      environment configuration
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) accumulator child)
    (facts : ExactCompilerWholeTraceCleanFacts parameters transitionFuel cursor
      masterTape)
    (alignment : NodeMachineRecordHasCausalState execution.base)
    (entryCovered :
      TableCoveredByQueryOrProgramming child.proverEntryOracle)
    (request : ConcreteRestorationRequest)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (parentFound : accumulator.node? request.nodeId = some child)
    (positive : request.verifierTransitionIndex ≠ 0)
    (transitionExact : verifierTransitionAt? child
      request.verifierTransitionIndex = some prepared.transition)
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator request = .ready prepared) :
    lookupEntry prepared.programmingBase prepared.outputInput = none ∧
      lookupEntry prepared.programmingBase prepared.advanceInput = none := by
  have provenance :=
    ready_positive_child_programming_base_query_and_programming_provenance
      execution facts alignment entryCovered request prepared parentFound
        positive ready
  have pairExact := prepare_from_start_ready_pair_inputs_exact startProgram
    configuration accumulator request prepared ready
  have inputsExact := squeeze_pair_inputs_exact_give_input_state
    prepared.transition prepared.outputInput prepared.advanceInput pairExact
  exact positive_transition_pair_lookups_none_of_query_absence execution facts
    prepared.programmingBase provenance.2.2 provenance.2.1
      request.verifierTransitionIndex prepared.transition positive
      transitionExact prepared.outputInput prepared.advanceInput inputsExact
      provenance.1

#print axioms active_exposure_answer_mem_accumulated_seen
#print axioms earlier_pair_before_is_prefix_of_current_trace_before
#print axioms operational_certificate_machine_record_has_causal_state
#print axioms projected_fresh_query_has_cumulative_request_state
#print axioms projected_fresh_trace_suffix_at_exact_prefix
#print axioms projected_fresh_query_at_exact_prefix_has_request_state
#print axioms projected_fresh_query_retains_entry_history_record
#print axioms projected_fresh_returned_trace_preserves_programming_history
#print axioms prior_programmed_input_state_ne_positive_transition_state
#print axioms prior_query_record_avoids_positive_transition_pair_inputs
#print axioms positive_transition_pair_absent_from_prover_entry_history
#print axioms ready_positive_child_programming_base_query_and_programming_provenance
#print axioms prior_programming_record_avoids_positive_transition_pair_inputs
#print axioms positive_transition_pair_lookups_none_of_query_absence
#print axioms ready_positive_child_programming_base_pair_lookups_none

end

end AspisK1.V7Tag73CausalProgrammingFreshness
