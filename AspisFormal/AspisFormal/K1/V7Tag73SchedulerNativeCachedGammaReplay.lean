import AspisFormal.K1.V7Tag73SchedulerNativeGammaReplay

/-!
# Cache-aware scheduler observation for Tag-73 gamma replay

`seekSchedulerNativeExposure` deliberately normalizes cached machine queries
before exposing the next fresh request.  Consequently a scan of only
`machineFresh` records can miss a gamma output or advance call whose answer
already occurs in the fixed oracle table.

This file exposes those normalized cached calls without changing the
production scheduler.  The observer is executable, consumes no master-tape
coordinate for a cached call, and records only calls actually traversed by
`seekNextFresh`.  A cache-aware target scan then either reports such a cached
call, pauses at the ordinary fresh request, or returns the complete absent
run.  Interpreting any branch reconstructs the literal scheduler run.

The cached branch is observational: it cannot replace a table answer.  Thus
it is sufficient for actual-run equality and for checking an actual duplex
coordinate, but it does not manufacture a counterfactual fresh coordinate.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeCachedGammaReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativeGammaReplay

noncomputable section

universe u

/-! ## The cached prefix hidden by `seekNextFresh` -/

structure CachedQueryObservation where
  record : QueryRecord
  originNonfresh : record.origin ≠ .fresh

/-- Cached calls executed by one invocation of `seekNextFresh`, in literal
chronological order.  Missing queries and terminal outcomes append nothing.
The definition duplicates no answer source: every recorded output is the
entry selected by the actual `lookupEntry` branch. -/
def cachedRecordsBeforeNextFresh {Result : Type u}
    (limits : OracleLimits) (actor : QueryActor) :
    Nat -> OracleState -> OracleMachine Result -> List CachedQueryObservation
  | _, _, .pure _ => []
  | _, _, .abort _ => []
  | 0, _, .query _ _ => []
  | fuel + 1, state, .query input next =>
      if state.totalCalls ≥ limits.totalCalls then
        []
      else
        match lookupEntry state input with
        | some entry =>
            { record :=
                { input := input
                  output := entry.output
                  actor := actor
                  origin := cachedOrigin entry.source }
              originNonfresh := by
                cases entry.source <;> simp [cachedOrigin] } ::
              cachedRecordsBeforeNextFresh limits actor fuel
                (cachedQueryState actor state input entry)
                (next entry.output)
        | none => []

/-- The cache observer is exactly the history suffix traversed by the
production normalizer. -/
theorem seek_next_fresh_history_eq_cached_records
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor) :
    forall (fuel : Nat) (state : OracleState)
      (program : OracleMachine Result)
      (coherent : HistoryTotalCoherent state),
      (seekNextFreshOracle
        (seekNextFresh limits actor fuel state program coherent)).history =
          state.history ++
            (cachedRecordsBeforeNextFresh limits actor fuel state program).map
              CachedQueryObservation.record := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program coherent
      cases program <;>
        simp [seekNextFresh, seekNextFreshOracle,
          cachedRecordsBeforeNextFresh]
  | succ fuel ih =>
      intro state program coherent
      cases program with
      | pure result =>
          simp [seekNextFresh, seekNextFreshOracle,
            cachedRecordsBeforeNextFresh]
      | abort reason =>
          simp [seekNextFresh, seekNextFreshOracle,
            cachedRecordsBeforeNextFresh]
      | query input next =>
          simp only [seekNextFresh, cachedRecordsBeforeNextFresh]
          split
          next totalBlocked => simp [seekNextFreshOracle]
          next totalRoom =>
            split
            next entry found =>
              simp only [seek_next_fresh_oracle_add_completed_query]
              rw [ih (cachedQueryState actor state input entry)
                (next entry.output)
                (cached_query_state_preserves_history_total_coherent actor
                  state input entry coherent)]
              simp [found, cachedQueryState, List.append_assoc]
            next missing =>
              simp only [missing]
              split <;> simp [seekNextFreshOracle]

/-- The table is not changed while normalizing a cached prefix. -/
theorem seek_next_fresh_oracle_table_eq
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor) :
    forall (fuel : Nat) (state : OracleState)
      (program : OracleMachine Result)
      (coherent : HistoryTotalCoherent state),
      (seekNextFreshOracle
        (seekNextFresh limits actor fuel state program coherent)).table =
          state.table := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program coherent
      cases program <;> rfl
  | succ fuel ih =>
      intro state program coherent
      cases program with
      | pure result => rfl
      | abort reason => rfl
      | query input next =>
          simp only [seekNextFresh]
          split
          next totalBlocked => rfl
          next totalRoom =>
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

/-! ## Cached calls across scheduler-native zero-exposure transitions -/

/-- All cached calls normalized before the next actual scheduler exposure.
Normal returns may install another machine cursor, so their cached suffixes
are concatenated while the transition budget decreases exactly as in
`seekSchedulerNativeExposure`. -/
def schedulerNativeCachedPrefix
    {globalOracleCalls : Nat} {Result : Type u} :
    Nat -> SchedulerNativeCursor globalOracleCalls Result ->
      List CachedQueryObservation
  | 0, _ => []
  | _ + 1, .returned _ => []
  | _ + 1, .failed _ => []
  | _ + 1, .forkPair .. => []
  | _ + 1, .forkAdvance .. => []
  | transitionFuel + 1,
      .machine limits _limitBound actor state program fuel coherent
        onReturned =>
      let currentRecords :=
        cachedRecordsBeforeNextFresh limits actor fuel state program
      match sought : seekNextFresh limits actor fuel state program coherent with
      | .returned result finalState _steps =>
          currentRecords ++ schedulerNativeCachedPrefix transitionFuel
            (onReturned result finalState
              (seek_next_fresh_returned_state_coherent limits actor fuel state
                finalState program coherent result _steps sought))
      | _ => currentRecords

/-- Find the first cached query at a selected input in one normalized
scheduler interval. -/
def firstCachedNativeInput
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (target : ShaInput) : Option CachedQueryObservation :=
  (schedulerNativeCachedPrefix transitionFuel cursor).find?
    (fun observation => observation.record.input = target)

theorem list_find_mem_of_some {Alpha : Type u}
    (predicate : Alpha -> Bool) :
    forall (values : List Alpha) (value : Alpha),
      values.find? predicate = some value -> value ∈ values := by
  intro values
  induction values with
  | nil =>
      intro value found
      simp at found
  | cons head tail ih =>
      intro value found
      simp only [List.find?] at found
      split at found
      next accepted =>
        cases found
        exact List.mem_cons_self
      next rejected =>
        exact List.mem_cons_of_mem head (ih value found)

theorem first_cached_native_input_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (target : ShaInput) (observation : CachedQueryObservation)
    (found : firstCachedNativeInput transitionFuel cursor target =
      some observation) :
    observation.record.input = target := by
  unfold firstCachedNativeInput at found
  have accepted := @List.find?_some CachedQueryObservation
    (fun candidate => decide (candidate.record.input = target)) observation
      (schedulerNativeCachedPrefix transitionFuel cursor) found
  exact of_decide_eq_true accepted

/-! ## Cache-aware target scan -/

structure SchedulerNativeCachedHit (target : ShaInput) where
  record : QueryRecord
  inputExact : record.input = target
  originNonfresh : record.origin ≠ .fresh

/-- A target can be observed in the normalized cached prefix, exposed as a
fresh request, or absent from the execution.  The cached branch retains the
already computed complete run; cached calls consume no answer coordinate. -/
inductive SchedulerNativeCachedTargetScan
    (globalOracleCalls : Nat) (Result : Type u) (target : ShaInput) where
  | cached (hit : SchedulerNativeCachedHit target)
      (run : SchedulerNativeRun Result)
  | fresh (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
  | absent (run : SchedulerNativeRun Result)

/-- Add one already executed exposure coordinate in front of a later
cache-aware scan result. -/
def SchedulerNativeCachedTargetScan.prepend
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (answer : Digest256) (record : UnifiedExposureRecord) :
    SchedulerNativeCachedTargetScan globalOracleCalls Result target ->
      SchedulerNativeCachedTargetScan globalOracleCalls Result target
  | .cached hit run =>
      .cached hit (prependSchedulerNativeRun record run)
  | .fresh pause => .fresh (pause.prepend answer record)
  | .absent run =>
      .absent (prependSchedulerNativeRun record run)

/-- Executable scan that checks the cached prefix before inspecting the next
fresh/fork exposure.  Recursion remains on the master-tape list; normalization
of cached calls is performed by the finite fuel-bounded machine semantics. -/
def scanSchedulerNativeCachedToInputFrom
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput) :
    (currentTransitionFuel : Nat) ->
      SchedulerNativeCursor globalOracleCalls Result -> List Digest256 ->
        SchedulerNativeCachedTargetScan globalOracleCalls Result target
  | currentTransitionFuel, cursor, answers =>
      match cachedFound :
          firstCachedNativeInput currentTransitionFuel cursor target with
      | some observation =>
          .cached
            { record := observation.record
              inputExact := first_cached_native_input_exact
                currentTransitionFuel cursor target observation cachedFound
              originNonfresh := observation.originNonfresh }
            (runSchedulerNativeListRunFrom transitionFuel
              currentTransitionFuel cursor answers)
      | none =>
          match answers with
          | [] =>
              .absent
                { terminal := terminalAtExposureEnd currentTransitionFuel cursor
                  trace := [] }
          | answer :: rest =>
              match requestExact :
                  seekSchedulerNativeExposure currentTransitionFuel cursor with
              | .returned result =>
                  (scanSchedulerNativeCachedToInputFrom transitionFuel target
                    transitionFuel
                    (.returned result :
                      SchedulerNativeCursor globalOracleCalls Result)
                    rest).prepend answer (.padding answer)
              | .failed reason =>
                  (scanSchedulerNativeCachedToInputFrom transitionFuel target
                    transitionFuel
                    (.failed reason :
                      SchedulerNativeCursor globalOracleCalls Result)
                    rest).prepend answer (.padding answer)
              | .transitionLimit =>
                  (scanSchedulerNativeCachedToInputFrom transitionFuel target
                    transitionFuel
                    (.failed .transitionLimit :
                      SchedulerNativeCursor globalOracleCalls Result)
                    rest).prepend answer (.padding answer)
              | .machineFresh limits limitBound actor requestState input
                  nextProgram remainingFuel coherent totalRoom freshRoom
                  missing onReturned =>
                  if input_eq_target : input = target then
                    .fresh
                      { MachineResult := _
                        limits := limits
                        limitBound := limitBound
                        actor := actor
                        requestState := requestState
                        input := input
                        input_eq_target := input_eq_target
                        nextProgram := nextProgram
                        remainingFuel := remainingFuel
                        coherent := coherent
                        totalRoom := totalRoom
                        freshRoom := freshRoom
                        missing := missing
                        onReturned := onReturned
                        sourceTransitionFuel := currentTransitionFuel
                        sourceCursor := cursor
                        requestExact := requestExact
                        consumedAnswers := []
                        consumedTrace := []
                        targetAnswer := answer
                        remainingAnswers := rest }
                  else
                    let nextCursor :
                        SchedulerNativeCursor globalOracleCalls Result :=
                      .machine limits limitBound actor
                        (freshQueryState actor requestState input answer)
                        (nextProgram answer) remainingFuel
                        (fresh_query_state_preserves_history_total_coherent actor
                          requestState input answer coherent) onReturned
                    (scanSchedulerNativeCachedToInputFrom transitionFuel target
                      transitionFuel nextCursor rest).prepend answer
                        (.machineFresh actor input answer)
              | .forkOutput frozenHistory pairRoom outputInput advanceInput
                  template next =>
                  let nextCursor :
                      SchedulerNativeCursor globalOracleCalls Result :=
                    .forkAdvance frozenHistory pairRoom outputInput advanceInput
                      template answer next
                  (scanSchedulerNativeCachedToInputFrom transitionFuel target
                    transitionFuel nextCursor rest).prepend answer
                      (.forkOutput frozenHistory outputInput advanceInput
                        template answer)
              | .forkAdvance frozenHistory _pairRoom outputInput advanceInput
                  template forkOutput next =>
                  let scheduled : ScheduledForkCoins :=
                    { frozenHistory := frozenHistory
                      outputInput := outputInput
                      advanceInput := advanceInput
                      template := template
                      forkOutput := forkOutput
                      forkAdvance := answer }
                  (scanSchedulerNativeCachedToInputFrom transitionFuel target
                    transitionFuel (next scheduled.configuration) rest).prepend
                      answer (.forkAdvance scheduled)

def scanSchedulerNativeCachedToInput
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    SchedulerNativeCachedTargetScan globalOracleCalls Result target :=
  scanSchedulerNativeCachedToInputFrom transitionFuel target transitionFuel
    cursor answers

/-- Interpret every cache-aware scan result as a complete scheduler run. -/
def SchedulerNativeCachedTargetScan.reconstructedRun
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat)
    (scan : SchedulerNativeCachedTargetScan globalOracleCalls Result target) :
    SchedulerNativeRun Result :=
  match scan with
  | .cached _ run => run
  | .fresh pause => pause.resumeRun transitionFuel
  | .absent run => run

@[simp] theorem SchedulerNativeCachedTargetScan.prepend_reconstructedRun
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat) (answer : Digest256)
    (record : UnifiedExposureRecord)
    (scan : SchedulerNativeCachedTargetScan globalOracleCalls Result target) :
    (scan.prepend answer record).reconstructedRun transitionFuel =
      prependSchedulerNativeRun record
        (scan.reconstructedRun transitionFuel) := by
  cases scan <;> rfl

/-- The cache-aware observer neither changes nor approximates execution.
Cached hits consume no answer; fresh hits resume on their retained answer;
all other exposure coordinates are interpreted by the production scheduler. -/
theorem scan_scheduler_native_cached_to_input_from_reconstructs_run
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput) :
    forall (currentTransitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256),
      (scanSchedulerNativeCachedToInputFrom transitionFuel target
        currentTransitionFuel cursor answers).reconstructedRun
          transitionFuel =
        runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
          cursor answers := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil =>
      simp only [scanSchedulerNativeCachedToInputFrom]
      split
      · rfl
      · rfl
  | cons answer rest ih =>
      simp only [scanSchedulerNativeCachedToInputFrom]
      split
      next observation cachedFound => rfl
      next cachedMissing =>
        simp only [runSchedulerNativeListRunFrom]
        split <;> rename_i requestExact
        all_goals simp only [requestExact]
        · rename_i result
          rw [SchedulerNativeCachedTargetScan.prepend_reconstructedRun]
          exact congrArg (prependSchedulerNativeRun (.padding answer))
            (ih transitionFuel
              (.returned result :
                SchedulerNativeCursor globalOracleCalls Result))
        · rename_i reason
          rw [SchedulerNativeCachedTargetScan.prepend_reconstructedRun]
          exact congrArg (prependSchedulerNativeRun (.padding answer))
            (ih transitionFuel
              (.failed reason :
                SchedulerNativeCursor globalOracleCalls Result))
        · rw [SchedulerNativeCachedTargetScan.prepend_reconstructedRun]
          exact congrArg (prependSchedulerNativeRun (.padding answer))
            (ih transitionFuel
              (.failed .transitionLimit :
                SchedulerNativeCursor globalOracleCalls Result))
        · rename_i MachineResult limits limitBound actor requestState input
            nextProgram remainingFuel coherent totalRoom freshRoom missing
            onReturned
          split
          next input_eq_target =>
            simp [SchedulerNativeCachedTargetScan.reconstructedRun,
              SchedulerNativeFreshPause.resumeRun,
              SchedulerNativeFreshPause.resumeRunWith,
              SchedulerNativeFreshPause.resumeCursorWith]
          next input_ne_target =>
            let nextCursor :
                SchedulerNativeCursor globalOracleCalls Result :=
              .machine limits limitBound actor
                (freshQueryState actor requestState input answer)
                (nextProgram answer) remainingFuel
                (fresh_query_state_preserves_history_total_coherent actor
                  requestState input answer coherent) onReturned
            rw [SchedulerNativeCachedTargetScan.prepend_reconstructedRun]
            exact congrArg
              (prependSchedulerNativeRun
                (.machineFresh actor input answer))
              (ih transitionFuel nextCursor)
        · rename_i frozenHistory pairRoom outputInput advanceInput template next
          let nextCursor : SchedulerNativeCursor globalOracleCalls Result :=
            .forkAdvance frozenHistory pairRoom outputInput advanceInput
              template answer next
          rw [SchedulerNativeCachedTargetScan.prepend_reconstructedRun]
          exact congrArg
            (prependSchedulerNativeRun
              (.forkOutput frozenHistory outputInput advanceInput template
                answer))
            (ih transitionFuel nextCursor)
        · rename_i frozenHistory pairRoom outputInput advanceInput template
            forkOutput next
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := answer }
          rw [SchedulerNativeCachedTargetScan.prepend_reconstructedRun]
          exact congrArg
            (prependSchedulerNativeRun (.forkAdvance scheduled))
            (ih transitionFuel (next scheduled.configuration))

theorem scan_scheduler_native_cached_to_input_reconstructs_run
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    SchedulerNativeCachedTargetScan.reconstructedRun transitionFuel
        (scanSchedulerNativeCachedToInput transitionFuel target cursor answers) =
      runSchedulerNativeListRun transitionFuel cursor answers := by
  exact scan_scheduler_native_cached_to_input_from_reconstructs_run
    transitionFuel target transitionFuel cursor answers

/-- A cached hit returns the exact production scheduler run while consuming
no distinguished master-tape coordinate. -/
theorem scan_scheduler_native_cached_hit_returns_actual
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) (hit : SchedulerNativeCachedHit target)
    (run : SchedulerNativeRun Result)
    (found : scanSchedulerNativeCachedToInput transitionFuel target cursor
      answers = .cached hit run) :
    run = runSchedulerNativeListRun transitionFuel cursor answers := by
  have exact := scan_scheduler_native_cached_to_input_reconstructs_run
    transitionFuel target cursor answers
  rw [found] at exact
  exact exact

/-- A fresh hit retains the old exact pause theorem inside the cache-aware
scan. -/
theorem scan_scheduler_native_cached_fresh_resume_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (found : scanSchedulerNativeCachedToInput transitionFuel target cursor
      answers = .fresh pause) :
    pause.resumeRun transitionFuel =
      runSchedulerNativeListRun transitionFuel cursor answers := by
  have exact := scan_scheduler_native_cached_to_input_reconstructs_run
    transitionFuel target cursor answers
  rw [found] at exact
  exact exact

/-! ## The cached-aware next-advance observer from an output pause -/

/-- After installing the actual output answer, the next advance lookup may be
cached.  This wrapper observes it before any later fresh exposure without
consuming another master-tape coordinate. -/
def cachedAdvanceAfterOutputPause
    {globalOracleCalls : Nat} {Result : Type u} {digest : Digest256}
    (transitionFuel : Nat)
    (outputPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput digest)) : Option CachedQueryObservation :=
  firstCachedNativeInput transitionFuel outputPause.resumeCursor
    (gammaAdvanceInput digest)

theorem cached_advance_after_output_pause_exact
    {globalOracleCalls : Nat} {Result : Type u} {digest : Digest256}
    (transitionFuel : Nat)
    (outputPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput digest))
    (observation : CachedQueryObservation)
    (found : cachedAdvanceAfterOutputPause transitionFuel outputPause =
      some observation) :
    observation.record.input = gammaAdvanceInput digest ∧
      observation.record.origin ≠ .fresh := by
  refine ⟨?_, observation.originNonfresh⟩
  exact first_cached_native_input_exact transitionFuel
    outputPause.resumeCursor (gammaAdvanceInput digest) observation found

#print axioms seek_next_fresh_history_eq_cached_records
#print axioms seek_next_fresh_oracle_table_eq
#print axioms first_cached_native_input_exact
#print axioms scan_scheduler_native_cached_to_input_from_reconstructs_run
#print axioms scan_scheduler_native_cached_to_input_reconstructs_run
#print axioms scan_scheduler_native_cached_hit_returns_actual
#print axioms scan_scheduler_native_cached_fresh_resume_exact
#print axioms cached_advance_after_output_pause_exact

end

end AspisK1.V7Tag73SchedulerNativeCachedGammaReplay
