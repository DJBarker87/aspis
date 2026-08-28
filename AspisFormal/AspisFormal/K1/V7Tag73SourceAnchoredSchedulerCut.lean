import AspisFormal.K1.V7Tag73SchedulerNativeCachedGammaReplay
import AspisFormal.K1.V7Tag73ProjectedMachinePrefix

/-!
# Source-anchored scheduler cuts

The exact projected machine semantics already retain the data needed for a
cursor-relative source statement: the current oracle state and residual
program, together with the ordered fresh queries that the literal production
continuation will still consume.  This file packages precisely that semantic
cut and derives the cache-or-future-fresh dichotomy from its executable trace
certificate.

No logical role, accepted proof, probability event, extraction statement, or
counterfactual conclusion is stored in the cut.  Cached calls are represented
by `seekNextFresh`; they change history but neither the immutable table nor the
ordered fresh-query suffix.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SourceAnchoredSchedulerCut

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeCachedGammaReplay
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeTargetPause

noncomputable section

universe u

/-- The table entry installed by one literal projected fresh query. -/
def projectedFreshEntry (query : ShaInput × Digest256) : TableEntry :=
  { input := query.1, output := query.2, source := .fresh }

/-- A semantic cut through one actual projected machine continuation.  Every
field is executable state or a literal `ProjectedFreshReturnedTrace`
certificate.  In particular, the structure does not store the derived lookup
dichotomy. -/
structure SourceAnchoredMachineCut
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (finalState : OracleState) (result : Result) where
  fuel : Nat
  state : OracleState
  program : OracleMachine Result
  remainingFresh : List (ShaInput × Digest256)
  steps : Nat
  trace : ProjectedFreshReturnedTrace limits actor fuel state program
    remainingFresh result finalState steps

/-- Every normally returned projected prefix canonically supplies a
source-anchored cut; no alignment fact is provided by a caller. -/
def SourceAnchoredMachineCut.ofProjectedPrefix
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    (fuel : Nat) (state : OracleState) (program : OracleMachine Result)
    (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    SourceAnchoredMachineCut limits actor returned.finalState
      returned.result :=
  { fuel := fuel
    state := state
    program := program
    remainingFresh := returned.freshQueries
    steps := returned.steps
    trace := returned.trace }

/-- Two literal projected machine segments joined at their actual intermediate
oracle state.  This is the minimal actor-change layer needed for the deployed
adversary-then-verifier root; it contains no role or probability data. -/
structure SourceAnchoredSequentialCut
    {FirstResult SecondResult : Type u}
    (firstLimits : OracleLimits) (firstActor : QueryActor)
    (secondLimits : OracleLimits) (secondActor : QueryActor)
    (middle finalState : OracleState)
    (firstResult : FirstResult) (secondResult : SecondResult) where
  first : SourceAnchoredMachineCut firstLimits firstActor middle firstResult
  second : SourceAnchoredMachineCut secondLimits secondActor finalState
    secondResult
  secondStartsAtMiddle : second.state = middle

/-- A projected continuation extends its current immutable table by exactly
the ordered fresh-query suffix carried by the trace certificate. -/
theorem projected_fresh_returned_trace_table_exact
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor) :
    forall (fuel : Nat) (state : OracleState)
      (program : OracleMachine Result)
      (freshQueries : List (ShaInput × Digest256)) (result : Result)
      (finalState : OracleState) (steps : Nat),
      ProjectedFreshReturnedTrace limits actor fuel state program
          freshQueries result finalState steps ->
        finalState.table =
          state.table ++ freshQueries.map projectedFreshEntry := by
  intro fuel state program freshQueries result finalState steps trace
  induction trace with
  | returned fuel state program coherent result finalState steps sought =>
      have tableExact := seek_next_fresh_oracle_table_eq limits actor fuel
        state program coherent
      rw [sought] at tableExact
      simpa [seekNextFreshOracle] using tableExact
  | fresh fuel state requestState program coherent input next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom missing sought answer rest
      result finalState tailSteps tail ih =>
      have prefixTable := seek_next_fresh_oracle_table_eq limits actor fuel
        state program coherent
      rw [sought] at prefixTable
      change requestState.table = state.table at prefixTable
      rw [ih, freshQueryState, prefixTable]
      simp [projectedFreshEntry, List.append_assoc]

/-- Table equation attached to a packaged source cut. -/
theorem SourceAnchoredMachineCut.table_exact
    {Result : Type u} {limits : OracleLimits} {actor : QueryActor}
    {finalState : OracleState} {result : Result}
    (cut : SourceAnchoredMachineCut limits actor finalState result) :
    finalState.table =
      cut.state.table ++ cut.remainingFresh.map projectedFreshEntry :=
  projected_fresh_returned_trace_table_exact limits actor cut.fuel cut.state
    cut.program cut.remainingFresh result finalState cut.steps cut.trace

private theorem lookup_entry_of_table_eq
    (left right : OracleState) (input : ShaInput)
    (tableExact : left.table = right.table) :
    lookupEntry left input = lookupEntry right input := by
  unfold lookupEntry
  rw [tableExact]

private theorem lookup_entry_append_of_some
    (state : OracleState) (suffix : List TableEntry)
    (input : ShaInput) (entry : TableEntry)
    (found : lookupEntry state input = some entry) :
    (state.table ++ suffix).find? (fun candidate => candidate.input = input) =
      some entry := by
  unfold lookupEntry at found
  rw [List.find?_append, found]
  rfl

private theorem lookup_output_append_mapped_fresh_of_missing
    (state : OracleState) (queries : List (ShaInput × Digest256))
    (input : ShaInput) (answer : Digest256)
    (missing : lookupEntry state input = none)
    (found :
      ((state.table ++ queries.map projectedFreshEntry).find?
          (fun candidate => candidate.input = input)).map TableEntry.output =
        some answer) :
    (input, answer) ∈ queries := by
  unfold lookupEntry at missing
  rw [List.find?_append, missing] at found
  cases suffixSelected :
      (queries.map projectedFreshEntry).find?
        (fun candidate => candidate.input = input) with
  | none => simp [suffixSelected] at found
  | some entry =>
  have outputExact : entry.output = answer := by
    simpa [suffixSelected] using found
  have inputExact : entry.input = input := by
    have accepted := @List.find?_some TableEntry
      (fun candidate => decide (candidate.input = input)) entry
      (queries.map projectedFreshEntry) suffixSelected
    exact of_decide_eq_true accepted
  have memberMapped : entry ∈ queries.map projectedFreshEntry :=
    List.mem_of_find?_eq_some suffixSelected
  rcases List.mem_map.mp memberMapped with ⟨query, queryMember, queryExact⟩
  rcases query with ⟨queryInput, queryAnswer⟩
  have queryInputExact : queryInput = input := by
    rw [← inputExact, ← queryExact]
    rfl
  have queryAnswerExact : queryAnswer = answer := by
    rw [← outputExact, ← queryExact]
    rfl
  simpa [queryInputExact, queryAnswerExact] using queryMember

/-- Every query in the projected fresh suffix is genuinely absent from the
table at the cut.  This is the chronological fact that prevents a later
projected fresh occurrence from duplicating an already cached coordinate. -/
theorem projected_fresh_returned_trace_future_input_missing
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor) :
    forall (fuel : Nat) (state : OracleState)
      (program : OracleMachine Result)
      (freshQueries : List (ShaInput × Digest256)) (result : Result)
      (finalState : OracleState) (steps : Nat)
      (trace : ProjectedFreshReturnedTrace limits actor fuel state program
        freshQueries result finalState steps)
      (input : ShaInput) (answer : Digest256),
      (input, answer) ∈ freshQueries -> lookupEntry state input = none := by
  intro fuel state program freshQueries result finalState steps trace
  induction trace with
  | returned fuel state program coherent result finalState steps sought =>
      intro input answer member
      simp at member
  | fresh fuel state requestState program coherent headInput next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom headMissing sought
      headAnswer rest result finalState tailSteps tail ih =>
      intro input answer member
      have prefixTable := seek_next_fresh_oracle_table_eq limits actor fuel
        state program coherent
      rw [sought] at prefixTable
      change requestState.table = state.table at prefixTable
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with head | later
      · rcases head with ⟨rfl, rfl⟩
        exact (lookup_entry_of_table_eq requestState state input
          prefixTable).symm.trans headMissing
      · have tailMissing := ih input answer later
        cases current : lookupEntry state input with
        | none => rfl
        | some entry =>
            have requestFound : lookupEntry requestState input = some entry :=
              (lookup_entry_of_table_eq requestState state input
                prefixTable).trans current
            have afterFound : lookupEntry
                (freshQueryState actor requestState headInput headAnswer)
                input = some entry := by
              unfold lookupEntry freshQueryState
              exact lookup_entry_append_of_some requestState
                [{ input := headInput, output := headAnswer, source := .fresh }]
                input entry requestFound
            rw [afterFound] at tailMissing
            contradiction

/-- Core cursor-relative dichotomy.  A lookup in the actual final state is
already immutable at the cut, or its exact input/answer pair occurs in the
ordered fresh suffix of the residual production program. -/
theorem source_anchored_machine_cut_lookup_or_future_fresh
    {Result : Type u} {limits : OracleLimits} {actor : QueryActor}
    {finalState : OracleState} {result : Result}
    (cut : SourceAnchoredMachineCut limits actor finalState result)
    (input : ShaInput) (answer : Digest256)
    (found : (lookupEntry finalState input).map TableEntry.output =
      some answer) :
    (exists entry,
        lookupEntry cut.state input = some entry /\ entry.output = answer) \/
      (input, answer) ∈ cut.remainingFresh := by
  cases current : lookupEntry cut.state input with
  | some entry =>
      left
      refine ⟨entry, rfl, ?_⟩
      have finalSelected : lookupEntry finalState input = some entry := by
        unfold lookupEntry
        rw [cut.table_exact]
        exact lookup_entry_append_of_some cut.state
          (cut.remainingFresh.map projectedFreshEntry) input entry current
      rw [finalSelected] at found
      simpa using found
  | none =>
      right
      unfold lookupEntry at found
      rw [cut.table_exact] at found
      exact lookup_output_append_mapped_fresh_of_missing cut.state
        cut.remainingFresh input answer current found

/-- One chronological fresh step produces another source-anchored cut.  The
cached normalization hidden in `seekNextFresh` leaves the table unchanged;
the step then appends exactly the actual head input/answer and exposes the
literal residual program and suffix. -/
theorem source_anchored_machine_cut_advance_first_fresh
    {Result : Type u} {limits : OracleLimits} {actor : QueryActor}
    {finalState : OracleState} {result : Result}
    (cut : SourceAnchoredMachineCut limits actor finalState result)
    (head : ShaInput × Digest256) (rest : List (ShaInput × Digest256))
    (remainingExact : cut.remainingFresh = head :: rest) :
    ∃ nextCut : SourceAnchoredMachineCut limits actor finalState result,
      nextCut.remainingFresh = rest ∧
      nextCut.state.table =
        cut.state.table ++ [projectedFreshEntry head] := by
  rcases cut with ⟨fuel, state, program, remainingFresh, steps, trace⟩
  change remainingFresh = head :: rest at remainingExact
  subst remainingFresh
  cases trace with
  | fresh fuel state requestState program coherent input next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom missing sought answer
      =>
      rename_i tailSteps tail
      have prefixTable := seek_next_fresh_oracle_table_eq limits actor fuel
        state program coherent
      rw [sought] at prefixTable
      change requestState.table = state.table at prefixTable
      refine ⟨{
        fuel := remainingFuel
        state := freshQueryState actor requestState input answer
        program := next answer
        remainingFresh := rest
        steps := tailSteps
        trace := tail }, rfl, ?_⟩
      simp [freshQueryState, projectedFreshEntry, prefixTable]

private theorem future_fresh_pair_has_projected_record
    (actor : QueryActor) (queries : List (ShaInput × Digest256))
    (input : ShaInput) (answer : Digest256)
    (future : (input, answer) ∈ queries) :
    (.machineFresh actor input answer : UnifiedExposureRecord) ∈
      projectedMachineFreshRecords actor queries := by
  induction queries with
  | nil => simp at future
  | cons query rest ih =>
      rcases query with ⟨headInput, headAnswer⟩
      simp only [List.mem_cons, Prod.mk.injEq] at future
      rcases future with head | later
      · rcases head with ⟨rfl, rfl⟩
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih later)

/-- Membership in the future-fresh branch names an exact chronological fresh
record for this machine actor. -/
theorem source_anchored_machine_cut_future_fresh_record
    {Result : Type u} {limits : OracleLimits} {actor : QueryActor}
    {finalState : OracleState} {result : Result}
    (cut : SourceAnchoredMachineCut limits actor finalState result)
    (input : ShaInput) (answer : Digest256)
    (future : (input, answer) ∈ cut.remainingFresh) :
    (.machineFresh actor input answer : UnifiedExposureRecord) ∈
      projectedMachineFreshRecords actor cut.remainingFresh := by
  exact future_fresh_pair_has_projected_record actor cut.remainingFresh input
    answer future

/-- Cursor-relative lookup/future routing across one actual actor change.  A
final answer is already cached at the first cut, or its original fresh
exposure remains in the first machine suffix, or it remains in the second
machine suffix. -/
theorem source_anchored_sequential_cut_lookup_or_ordered_future_fresh
    {FirstResult SecondResult : Type u}
    {firstLimits secondLimits : OracleLimits}
    {firstActor secondActor : QueryActor}
    {middle finalState : OracleState}
    {firstResult : FirstResult} {secondResult : SecondResult}
    (cut : SourceAnchoredSequentialCut firstLimits firstActor secondLimits
      secondActor middle finalState firstResult secondResult)
    (input : ShaInput) (answer : Digest256)
    (found : (lookupEntry finalState input).map TableEntry.output =
      some answer) :
    (exists entry,
        lookupEntry cut.first.state input = some entry /\
          entry.output = answer) \/
      (input, answer) ∈ cut.first.remainingFresh \/
      (input, answer) ∈ cut.second.remainingFresh := by
  rcases source_anchored_machine_cut_lookup_or_future_fresh cut.second input
      answer found with cachedAtMiddle | futureSecond
  · rcases cachedAtMiddle with ⟨entry, selected, outputExact⟩
    have selectedAtMiddle : lookupEntry middle input = some entry := by
      rw [← cut.secondStartsAtMiddle]
      exact selected
    have foundAtMiddle :
        (lookupEntry middle input).map TableEntry.output = some answer := by
      simp [selectedAtMiddle, outputExact]
    rcases source_anchored_machine_cut_lookup_or_future_fresh cut.first input
        answer foundAtMiddle with cachedAtFirst | futureFirst
    · exact Or.inl cachedAtFirst
    · exact Or.inr (Or.inl futureFirst)
  · exact Or.inr (Or.inr futureSecond)

/-! ## Native scan of one projected machine continuation -/

/-- A future projected fresh pair forces the executable scheduler-native
scanner to pause at this input with the exact actual answer at that
chronological coordinate.  This is cursor-relative: the literal projected
suffix is the head of the remaining master tape. -/
theorem projected_fresh_trace_scan_pauses_at_exact_future_answer
    {globalOracleCalls : Nat} {Final MachineResult : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) -> (state : OracleState) ->
      HistoryTotalCoherent state ->
        AspisK1.V7Tag73SchedulerNativeResult.SchedulerNativeCursor
          globalOracleCalls Final)
    {fuel : Nat} {state : OracleState}
    {program : OracleMachine MachineResult}
    {freshQueries : List (ShaInput × Digest256)}
    {result : MachineResult} {finalState : OracleState} {steps : Nat}
    (coherent : HistoryTotalCoherent state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps)
    (suffix : List Digest256) (input : ShaInput) (answer : Digest256)
    (future : (input, answer) ∈ freshQueries) :
    exists pause,
      scanSchedulerNativeToInput
          transitionFuel input
          (.machine limits limitBound actor state program fuel coherent
            onReturned)
          (freshQueries.map Prod.snd ++ suffix) = .paused pause /\
        pause.targetAnswer = answer := by
  induction trace generalizing suffix input answer with
  | returned fuel state program traceCoherent result finalState steps sought =>
      simp at future
  | fresh fuel state requestState program traceCoherent headInput nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought headAnswer rest result finalState tailSteps tail ih =>
      have coherentExact : coherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      cases transitionFuel with
      | zero => omega
      | succ current =>
          simp only [List.mem_cons, Prod.mk.injEq] at future
          rcases future with head | later
          · rcases head with ⟨rfl, rfl⟩
            have normalized :=
              seek_scheduler_native_exposure_machine_of_fresh current limits
                limitBound actor fuel state requestState program traceCoherent
                input nextProgram remainingFuel cachedSteps requestCoherent
                totalRoom freshRoom missing onReturned sought
            simp only [List.map_cons, List.cons_append,
              scanSchedulerNativeToInput, scanSchedulerNativeToInputFrom]
            split <;> rename_i requestExact
            all_goals rw [normalized] at requestExact
            all_goals cases requestExact
            simp
          · have different : headInput ≠ input := by
              intro equal
              subst input
              have tailMissing :=
                projected_fresh_returned_trace_future_input_missing limits actor
                  remainingFuel
                  (freshQueryState actor requestState headInput headAnswer)
                  (nextProgram headAnswer) rest result finalState tailSteps tail
                  headInput answer later
              unfold lookupEntry freshQueryState at tailMissing
              unfold lookupEntry at missing
              rw [List.find?_append, missing] at tailMissing
              simp at tailMissing
            obtain ⟨pause, paused, answerExact⟩ := ih
              (fresh_query_state_preserves_history_total_coherent actor
                requestState headInput headAnswer requestCoherent)
              suffix input answer later
            refine ⟨pause.prepend headAnswer
              (.machineFresh actor headInput headAnswer), ?_, answerExact⟩
            have normalized :=
              seek_scheduler_native_exposure_machine_of_fresh current limits
                limitBound actor fuel state requestState program traceCoherent
                headInput nextProgram remainingFuel cachedSteps
                requestCoherent totalRoom freshRoom missing onReturned sought
            simp only [List.map_cons, List.cons_append,
              scanSchedulerNativeToInput, scanSchedulerNativeToInputFrom]
            split <;> rename_i requestExact
            all_goals rw [normalized] at requestExact
            all_goals cases requestExact
            split
            · rename_i equal
              exact (different equal).elim
            · rename_i notEqual
              rename_i limitBound2 coherent2 totalRoom2 freshRoom2 missing2
              have limitBoundExact : limitBound2 = limitBound :=
                Subsingleton.elim _ _
              cases limitBoundExact
              have coherentProofExact : coherent2 = requestCoherent :=
                Subsingleton.elim _ _
              cases coherentProofExact
              have totalRoomExact : totalRoom2 = totalRoom :=
                Subsingleton.elim _ _
              cases totalRoomExact
              have freshRoomExact : freshRoom2 = freshRoom :=
                Subsingleton.elim _ _
              cases freshRoomExact
              have missingExact : missing2 = missing := Subsingleton.elim _ _
              cases missingExact
              unfold scanSchedulerNativeToInput at paused
              simp only [paused]

/-- Answer-erased corollary used by callers that only need reachability. -/
theorem projected_fresh_trace_scan_pauses_at_future_input
    {globalOracleCalls : Nat} {Final MachineResult : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) -> (state : OracleState) ->
      HistoryTotalCoherent state ->
        AspisK1.V7Tag73SchedulerNativeResult.SchedulerNativeCursor
          globalOracleCalls Final)
    {fuel : Nat} {state : OracleState}
    {program : OracleMachine MachineResult}
    {freshQueries : List (ShaInput × Digest256)}
    {result : MachineResult} {finalState : OracleState} {steps : Nat}
    (coherent : HistoryTotalCoherent state)
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps)
    (suffix : List Digest256) (input : ShaInput) (answer : Digest256)
    (future : (input, answer) ∈ freshQueries) :
    exists pause,
      scanSchedulerNativeToInput
          transitionFuel input
          (.machine limits limitBound actor state program fuel coherent
            onReturned)
          (freshQueries.map Prod.snd ++ suffix) = .paused pause := by
  obtain ⟨pause, paused, _answerExact⟩ :=
    projected_fresh_trace_scan_pauses_at_exact_future_answer transitionFuel
      positive limits limitBound actor onReturned coherent trace suffix input
      answer future
  exact ⟨pause, paused⟩

/-- Reusable one-coordinate consumption boundary for an aligned machine cut.
An actual final-table answer is either already immutable at the cut, or the
executable native scanner reaches a fresh request for the same input on the
literal remaining production tape. -/
theorem source_anchored_machine_cut_lookup_or_scan_pause
    {globalOracleCalls : Nat} {Final MachineResult : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) -> (state : OracleState) ->
      HistoryTotalCoherent state ->
        AspisK1.V7Tag73SchedulerNativeResult.SchedulerNativeCursor
          globalOracleCalls Final)
    {finalState : OracleState} {result : MachineResult}
    (cut : SourceAnchoredMachineCut limits actor finalState result)
    (coherent : HistoryTotalCoherent cut.state)
    (suffix : List Digest256) (input : ShaInput) (answer : Digest256)
    (found : (lookupEntry finalState input).map TableEntry.output =
      some answer) :
    (exists entry,
        lookupEntry cut.state input = some entry /\ entry.output = answer) \/
      exists pause,
        AspisK1.V7Tag73SchedulerNativeTargetPause.scanSchedulerNativeToInput
            transitionFuel input
            (.machine limits limitBound actor cut.state cut.program cut.fuel
              coherent onReturned)
            (cut.remainingFresh.map Prod.snd ++ suffix) = .paused pause /\
          pause.targetAnswer = answer := by
  rcases source_anchored_machine_cut_lookup_or_future_fresh cut input answer
      found with cached | future
  · exact Or.inl cached
  · exact Or.inr
      (projected_fresh_trace_scan_pauses_at_exact_future_answer transitionFuel
        positive limits limitBound actor onReturned coherent cut.trace suffix
        input answer future)

#print axioms projected_fresh_returned_trace_future_input_missing
#print axioms projected_fresh_trace_scan_pauses_at_exact_future_answer
#print axioms projected_fresh_trace_scan_pauses_at_future_input
#print axioms source_anchored_machine_cut_lookup_or_scan_pause

#print axioms projected_fresh_returned_trace_table_exact
#print axioms SourceAnchoredMachineCut.table_exact
#print axioms source_anchored_machine_cut_lookup_or_future_fresh
#print axioms source_anchored_machine_cut_advance_first_fresh
#print axioms source_anchored_machine_cut_future_fresh_record
#print axioms source_anchored_sequential_cut_lookup_or_ordered_future_fresh

end

end AspisK1.V7Tag73SourceAnchoredSchedulerCut
