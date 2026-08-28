import AspisFormal.K1.V7Tag73SourceAnchoredSchedulerCut
import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal
import AspisFormal.K1.V7Tag73SchedulerNativePausePrefixBridge
import AspisFormal.K1.V7Tag73K12BudgetedSchedulerTree
import AspisFormal.K1.V7Tag73ExactCompilerSourceAnchoredCut

/-!
# Native cursor factorization of a source-anchored machine cut

This file proves the missing executable half of a residual source cut.  A
literal prefix of the cut's projected fresh-answer list computes the native
scheduler cursor whose machine state, residual program, and fuel are exactly
those of the residual cut.  The statement is machine-local and contains no
protocol role, replay conclusion, or probability premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73SourceAnchoredNativeCursorFactorization

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativePausePrefixBridge
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativeCachedGammaReplay
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SourceAnchoredSchedulerCut
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73RootSuccessForcesFullCompletion
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut

noncomputable section

universe u

/-- The start state of a returned projected trace carries its literal
history-coherence proof. -/
theorem projected_fresh_returned_trace_start_coherent
    {Result : Type u} {limits : OracleLimits} {actor : QueryActor}
    {fuel : Nat} {state : OracleState} {program : OracleMachine Result}
    {freshQueries : List (ShaInput × Digest256)} {result : Result}
    {finalState : OracleState} {steps : Nat}
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps) :
    HistoryTotalCoherent state := by
  cases trace with
  | returned fuel state program coherent result finalState steps sought =>
      exact coherent
  | fresh fuel state requestState program coherent input next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom missing sought answer rest
      result finalState tailSteps tail =>
      exact coherent

/-- Consuming a literal fresh-query prefix reaches exactly the residual
source cut as a native machine cursor. -/
theorem source_anchored_machine_cut_native_cursor_after_prefix
    {globalOracleCalls : Nat} {Final Result : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : Result) → (state : OracleState) →
      HistoryTotalCoherent state → SchedulerNativeCursor globalOracleCalls Final)
    {finalState : OracleState} {result : Result}
    (cut : SourceAnchoredMachineCut limits actor finalState result) :
    ∀ (prior suffix : List (ShaInput × Digest256)),
      cut.remainingFresh = prior ++ suffix →
      ∃ (nextCut : SourceAnchoredMachineCut limits actor finalState result)
        (nextCoherent : HistoryTotalCoherent nextCut.state),
        nextCut.remainingFresh = suffix ∧
        nextCut.state.table =
          cut.state.table ++ prior.map projectedFreshEntry ∧
        schedulerNativePrefixCursor transitionFuel
            (.machine limits limitBound actor cut.state cut.program cut.fuel
              (projected_fresh_returned_trace_start_coherent cut.trace)
              onReturned)
            (prior.map Prod.snd) =
          .machine limits limitBound actor nextCut.state nextCut.program
            nextCut.fuel nextCoherent onReturned := by
  intro prior
  induction prior generalizing cut with
  | nil =>
      intro suffix remainingExact
      refine ⟨cut, projected_fresh_returned_trace_start_coherent cut.trace,
        ?_, ?_, ?_⟩
      · simpa using remainingExact
      · simp
      · rfl
  | cons head rest ih =>
      intro suffix remainingExact
      rcases head with ⟨headInput, headAnswer⟩
      rcases cut with ⟨fuel, state, program, remainingFresh, steps, trace⟩
      change remainingFresh =
        (headInput, headAnswer) :: rest ++ suffix at remainingExact
      subst remainingFresh
      cases trace with
      | fresh fuel state requestState program coherent input next remainingFuel
          cachedSteps requestCoherent totalRoom freshRoom missing sought answer
          tailFresh result finalState tailSteps tail =>
          let afterHead : SourceAnchoredMachineCut limits actor finalState
              result :=
            { fuel := remainingFuel
              state := freshQueryState actor requestState headInput headAnswer
              program := next headAnswer
              remainingFresh := rest ++ suffix
              steps := tailSteps
              trace := tail }
          obtain ⟨nextCut, nextCoherent, nextRemaining, nextTable,
              cursorExact⟩ :=
            ih afterHead suffix rfl
          refine ⟨nextCut, nextCoherent, nextRemaining, ?_, ?_⟩
          · have prefixTable := seek_next_fresh_oracle_table_eq limits actor
              fuel state program coherent
            rw [sought] at prefixTable
            change requestState.table = state.table at prefixTable
            rw [nextTable]
            simp [afterHead, freshQueryState, prefixTable,
              projectedFreshEntry, List.map_cons, List.append_assoc]
          cases transitionFuel with
          | zero => omega
          | succ current =>
              simp only [List.map_cons, schedulerNativePrefixCursor]
              rw [seek_scheduler_native_exposure_machine_of_fresh current
                limits limitBound actor fuel state requestState program
                coherent headInput next remainingFuel cachedSteps requestCoherent
                totalRoom freshRoom missing onReturned sought]
              exact cursorExact

/-- Once the next normalized native request agrees, consuming a nonempty
answer prefix computes the same successor cursor.  This is the actor-neutral
bridge used when the first answer after a machine return belongs to the next
machine callback. -/
theorem scheduler_native_prefix_cursor_cons_congr_of_seek_eq
    {globalOracleCalls : Nat} {Final : Type u}
    (transitionFuel : Nat)
    (left right : SchedulerNativeCursor globalOracleCalls Final)
    (answer : Digest256) (rest : List Digest256)
    (aligned : seekSchedulerNativeExposure transitionFuel left =
      seekSchedulerNativeExposure transitionFuel right) :
    schedulerNativePrefixCursor transitionFuel left (answer :: rest) =
      schedulerNativePrefixCursor transitionFuel right (answer :: rest) := by
  simp only [schedulerNativePrefixCursor]
  rw [aligned]

/-- The corresponding chronological record prefix is identical as well. -/
theorem scheduler_native_prefix_records_cons_congr_of_seek_eq
    {globalOracleCalls : Nat} {Final : Type u}
    (transitionFuel : Nat)
    (left right : SchedulerNativeCursor globalOracleCalls Final)
    (answer : Digest256) (rest : List Digest256)
    (aligned : seekSchedulerNativeExposure transitionFuel left =
      seekSchedulerNativeExposure transitionFuel right) :
    schedulerNativePrefixRecords transitionFuel left (answer :: rest) =
      schedulerNativePrefixRecords transitionFuel right (answer :: rest) := by
  simp only [schedulerNativePrefixRecords, aligned]

/-- Two decompositions of the same list are comparable by prefix. -/
theorem append_eq_append_prefix_split {α : Type u} :
    ∀ (left right consumed future : List α),
      left ++ right = consumed ++ future →
      (∃ suffix, left = consumed ++ suffix ∧ future = suffix ++ right) ∨
      (∃ suffix, consumed = left ++ suffix ∧ right = suffix ++ future) := by
  intro left
  induction left with
  | nil =>
      intro right consumed future exact
      right
      exact ⟨consumed, by simp, by simpa using exact⟩
  | cons head tail ih =>
      intro right consumed future exact
      cases consumed with
      | nil =>
          left
          exact ⟨head :: tail, by simp, by simpa using exact.symm⟩
      | cons consumedHead consumedTail =>
          simp only [List.cons_append, List.cons.injEq] at exact
          rcases exact with ⟨headExact, tailExact⟩
          subst consumedHead
          rcases ih right consumedTail future tailExact with split | split
          · rcases split with ⟨suffix, leftExact, futureExact⟩
            left
            exact ⟨suffix, by simp [leftExact], futureExact⟩
          · rcases split with ⟨suffix, consumedExact, rightExact⟩
            right
            exact ⟨suffix, by simp [consumedExact], rightExact⟩

/-- The evolving root split is at exactly one of the two literal production
machines: either the consumed prefix is still inside the adversary segment,
or it contains that segment and is inside the verifier segment. -/
theorem exact_compiler_alignment_actor_phase_split
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (aligned : ExactCompilerRootGammaCursorAligned input state) :
    (∃ adversaryFuture,
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        aligned.consumed ++ adversaryFuture ∧
      aligned.future = adversaryFuture ++
        input.package.root.full.projection.rootPrefixes.verifier.freshQueries) ∨
    (∃ verifierConsumed,
      aligned.consumed =
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
          verifierConsumed ∧
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        verifierConsumed ++ aligned.future) := by
  exact append_eq_append_prefix_split _ _ _ _ aligned.rootSplit

/-- Positional form of the actor split at a selected coordinate of the
aligned future.  The three cases are: target in the residual adversary,
target in the verifier while the cursor is still in the adversary, and target
in the residual verifier. -/
theorem exact_compiler_alignment_selected_coordinate_phase_split
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (prior later : List (ShaInput × Digest256))
    (selected : ShaInput × Digest256)
    (futureExact : aligned.future = prior ++ selected :: later) :
    (∃ adversaryLater,
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        aligned.consumed ++ prior ++ selected :: adversaryLater ∧
      later = adversaryLater ++
        input.package.root.full.projection.rootPrefixes.verifier.freshQueries) ∨
    (∃ adversaryFuture verifierPrior,
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        aligned.consumed ++ adversaryFuture ∧
      prior = adversaryFuture ++ verifierPrior ∧
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        verifierPrior ++ selected :: later) ∨
    (∃ verifierConsumed,
      aligned.consumed =
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
          verifierConsumed ∧
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        verifierConsumed ++ prior ++ selected :: later) := by
  rcases exact_compiler_alignment_actor_phase_split aligned with
      ⟨adversaryFuture, adversaryExact, futurePhase⟩ |
      ⟨verifierConsumed, consumedExact, verifierExact⟩
  · have joined : adversaryFuture ++
        input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
      prior ++ selected :: later := by
      rw [← futurePhase, futureExact]
    rcases append_eq_append_prefix_split adversaryFuture
        input.package.root.full.projection.rootPrefixes.verifier.freshQueries
        prior (selected :: later) joined with
      ⟨suffix, adversarySuffix, tailSuffix⟩ |
      ⟨verifierPrior, priorExact, verifierSuffix⟩
    · cases suffix with
      | nil =>
          right
          left
          refine ⟨adversaryFuture, [], adversaryExact, ?_, ?_⟩
          · simpa using adversarySuffix.symm
          · simpa using tailSuffix.symm
      | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at tailSuffix
          rcases tailSuffix with ⟨selectedExact, laterExact⟩
          subst head
          left
          refine ⟨tail, ?_, laterExact⟩
          rw [adversaryExact, adversarySuffix, List.append_assoc]
    · right
      left
      exact ⟨adversaryFuture, verifierPrior, adversaryExact, priorExact,
        verifierSuffix⟩
  · right
    right
    refine ⟨verifierConsumed, consumedExact, ?_⟩
    rw [verifierExact, futureExact, List.append_assoc]

/-! ## Exact adversary-to-verifier boundary -/

/-- After all adversary fresh answers have been consumed, normalizing the
literal production cursor exposes exactly the same next request as the
deployed verifier cursor.  The verifier nonemptiness is the honest condition
under which the one transition spent returning through the adversary callback
cannot affect the exposed request. -/
theorem exact_compiler_adversary_boundary_seek_eq_verifier
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (verifierNonempty :
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries ≠
        []) :
    let prefixes := input.package.root.full.projection.rootPrefixes
    seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (prefixes.adversary.freshQueries.map Prod.snd)) =
      seekSchedulerNativeExposure transitionFuel
        (fullRootVerifierCursor configuration sample.1
          prefixes.adversaryValue prefixes.adversary.finalState
          prefixes.adversary.finalCoherent) := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  dsimp only
  have positive : 0 < transitionFuel := by omega
  have rootListCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (exactPlainRomRootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        .returned (.completed input.package.root.fixedRoot.base.runtime
          input.package.root.fixedRoot.base.clientRun) := by
    rw [← run_scheduler_native_terminal_eq_list]
    exact input.package.root.fixedRoot.base.rootCompleted
  let stages := completed_root_constructs_operational_stages transitionFuel
    positive configuration.machine sample.1 configuration.rootLimitBounds
    configuration.restorationConfiguration (freshAnswerTapeToList sample.2)
    input.package.root.fixedRoot.base.runtime
    input.package.root.fixedRoot.base.clientRun (by
      simpa [exactPlainRomRootCursor] using rootListCompleted)
  have adversaryExact :=
    completed_root_stages_and_full_prefix_adversary_exact
      (Result := Result) stages prefixes
  have verifierRoom : StageHasOracleRoom
      configuration.machine.verifierLimits prefixes.adversary.finalState
      configuration.machine.verifierFuel := by
    simpa only [← adversaryExact.2] using stages.verifierRoom
  have rootCursorExact := exact_plain_rom_cursor_eq_root_machine_of_room
    configuration sample.1 stages.adversaryRoom
  have adversaryCallbackExact :
      fullRootAdversaryReturnedContinuation configuration sample.1
          prefixes.adversary.result prefixes.adversary.finalState
          prefixes.adversary.finalCoherent =
        fullRootVerifierCursor configuration sample.1
          prefixes.adversaryValue prefixes.adversary.finalState
          prefixes.adversary.finalCoherent := by
    rw [prefixes.adversaryResult]
    simp only [fullRootAdversaryReturnedContinuation, if_pos verifierRoom]
  rw [rootCursorExact]
  calc
    seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel
          (.machine configuration.machine.adversaryLimits
            configuration.rootLimitBounds.adversary .adversary emptyOracle
            (schedulerStageProgram
              (SchedulerNativePlainRomResult TapeIdentity Statement
                Tag73K12ParsedProof Payload Result)
              (totalizeOracleMachine configuration.machine.adversaryFuel
                (configuration.machine.blackBox.start sample.1
                  configuration.machine.observation)))
            configuration.machine.adversaryFuel
            empty_oracle_history_total_coherent
            (fullRootAdversaryReturnedContinuation configuration sample.1))
          (prefixes.adversary.freshQueries.map Prod.snd)) =
      seekSchedulerNativeExposure transitionFuel
        (fullRootAdversaryReturnedContinuation configuration sample.1
          prefixes.adversary.result prefixes.adversary.finalState
          prefixes.adversary.finalCoherent) :=
      (projected_machine_prefix_reaches_returned_native_predecessor_for_k12
        transitionFuel positive configuration.machine.adversaryLimits
        configuration.rootLimitBounds.adversary .adversary
        configuration.machine.adversaryFuel emptyOracle
        (schedulerStageProgram
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)
          (totalizeOracleMachine configuration.machine.adversaryFuel
            (configuration.machine.blackBox.start sample.1
              configuration.machine.observation)))
        empty_oracle_history_total_coherent
        (fullRootAdversaryReturnedContinuation configuration sample.1)
        (freshAnswerTapeToList sample.2) prefixes.adversary).trans
        (by
          rw [adversaryCallbackExact]
          apply projected_nonempty_fresh_prefix_seek_predecessor_eq_for_k12
            transitionFuel transitionRoom
            configuration.machine.verifierLimits
            configuration.rootLimitBounds.verifier .verifier
            configuration.machine.verifierFuel
            prefixes.adversary.finalState
            (schedulerStageProgram
              (SchedulerNativePlainRomResult TapeIdentity Statement
                Tag73K12ParsedProof Payload Result)
              (totalizeOracleMachine configuration.machine.verifierFuel
                (initialRawFutureFreeProgram configuration.machine.environment
                  prefixes.adversaryValue.rawMessages
                  configuration.machine.driverFuel)))
            prefixes.adversary.finalCoherent
            (fullRootVerifierReturnedContinuation configuration sample.1
              prefixes.adversaryValue prefixes.adversary.finalState)
            prefixes.verifier.trace verifierNonempty)
    _ = _ := adversaryCallbackExact ▸ rfl

/-- Any adversary fresh prefix is reached by the literal full root cursor, and
the resulting cursor is exactly the residual adversary source cut. -/
theorem exact_compiler_root_cursor_after_adversary_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (adversaryPrior adversaryLater : List (ShaInput × Digest256))
    (adversarySplit :
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        adversaryPrior ++ adversaryLater) :
    ∃ (nextCut : SourceAnchoredMachineCut
        configuration.machine.adversaryLimits .adversary
        input.package.root.full.projection.rootPrefixes.adversary.finalState
        input.package.root.full.projection.rootPrefixes.adversary.result)
      (nextCoherent : HistoryTotalCoherent nextCut.state),
      nextCut.remainingFresh = adversaryLater ∧
      nextCut.state.table = adversaryPrior.map projectedFreshEntry ∧
      schedulerNativePrefixCursor transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (adversaryPrior.map Prod.snd) =
        .machine configuration.machine.adversaryLimits
          configuration.rootLimitBounds.adversary .adversary nextCut.state
          nextCut.program nextCut.fuel nextCoherent
          (fullRootAdversaryReturnedContinuation configuration sample.1) := by
  have positive : 0 < transitionFuel := by omega
  have rootListCompleted :
      runSchedulerNativeListTerminal transitionFuel
          (exactPlainRomRootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        .returned (.completed input.package.root.fixedRoot.base.runtime
          input.package.root.fixedRoot.base.clientRun) := by
    rw [← run_scheduler_native_terminal_eq_list]
    exact input.package.root.fixedRoot.base.rootCompleted
  let stages := completed_root_constructs_operational_stages transitionFuel
    positive configuration.machine sample.1 configuration.rootLimitBounds
    configuration.restorationConfiguration (freshAnswerTapeToList sample.2)
    input.package.root.fixedRoot.base.runtime
    input.package.root.fixedRoot.base.clientRun (by
      simpa [exactPlainRomRootCursor] using rootListCompleted)
  have rootCursorExact := exact_plain_rom_cursor_eq_root_machine_of_room
    configuration sample.1 stages.adversaryRoom
  let adversaryCut := (exactCompilerRootSourceAnchoredCut input).first
  obtain ⟨nextCut, nextCoherent, nextRemaining, nextTable, localCursor⟩ :=
    source_anchored_machine_cut_native_cursor_after_prefix transitionFuel
      positive configuration.machine.adversaryLimits
      configuration.rootLimitBounds.adversary .adversary
      (fullRootAdversaryReturnedContinuation configuration sample.1)
      adversaryCut adversaryPrior adversaryLater (by
        simpa [adversaryCut] using adversarySplit)
  refine ⟨nextCut, nextCoherent, nextRemaining, ?_, ?_⟩
  · change nextCut.state.table =
      emptyOracle.table ++ adversaryPrior.map projectedFreshEntry at nextTable
    simpa only [emptyOracle, List.nil_append] using nextTable
  rw [rootCursorExact]
  dsimp only [adversaryCut, exactCompilerRootSourceAnchoredCut,
    SourceAnchoredMachineCut.ofProjectedPrefix] at localCursor
  exact localCursor

/-- Any nonempty verifier fresh prefix is reached by the literal full root
cursor, and the resulting cursor is exactly the residual verifier source cut.
This is the sequential specialization missing from the two-cut table router. -/
theorem exact_compiler_root_cursor_after_nonempty_verifier_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (verifierPrior verifierLater : List (ShaInput × Digest256))
    (verifierSplit :
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        verifierPrior ++ verifierLater)
    (priorNonempty : verifierPrior ≠ []) :
    ∃ (nextCut : SourceAnchoredMachineCut
        configuration.machine.verifierLimits .verifier
        input.package.root.full.projection.rootPrefixes.verifier.finalState
        input.package.root.full.projection.rootPrefixes.verifier.result)
      (nextCoherent : HistoryTotalCoherent nextCut.state),
      nextCut.remainingFresh = verifierLater ∧
      nextCut.state.table =
        (input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
          verifierPrior).map projectedFreshEntry ∧
      schedulerNativePrefixCursor transitionFuel
          (exactPlainRomCursor configuration sample.1)
          ((input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
            verifierPrior).map Prod.snd) =
        .machine configuration.machine.verifierLimits
          configuration.rootLimitBounds.verifier .verifier nextCut.state
          nextCut.program nextCut.fuel nextCoherent
          (fullRootVerifierReturnedContinuation configuration sample.1
            input.package.root.full.projection.rootPrefixes.adversaryValue
            input.package.root.full.projection.rootPrefixes.adversary.finalState) := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have verifierNonempty : prefixes.verifier.freshQueries ≠ [] := by
    rw [verifierSplit]
    simp [priorNonempty]
  have boundary := exact_compiler_adversary_boundary_seek_eq_verifier
    transitionRoom input verifierNonempty
  let verifierCut :=
    (exactCompilerRootSourceAnchoredCut input).second
  obtain ⟨nextCut, nextCoherent, nextRemaining, nextTable, localCursor⟩ :=
    source_anchored_machine_cut_native_cursor_after_prefix transitionFuel
      (by omega) configuration.machine.verifierLimits
      configuration.rootLimitBounds.verifier .verifier
      (fullRootVerifierReturnedContinuation configuration sample.1
        prefixes.adversaryValue prefixes.adversary.finalState)
      verifierCut verifierPrior verifierLater (by
        simpa [verifierCut, prefixes] using verifierSplit)
  refine ⟨nextCut, nextCoherent, nextRemaining, ?_, ?_⟩
  · have adversaryTable :=
      (exactCompilerRootSourceAnchoredCut input).first.table_exact
    have verifierStartTable : verifierCut.state.table =
        prefixes.adversary.freshQueries.map projectedFreshEntry := by
      change prefixes.adversary.finalState.table = _
      change prefixes.adversary.finalState.table =
        emptyOracle.table ++
          prefixes.adversary.freshQueries.map projectedFreshEntry at adversaryTable
      simpa only [emptyOracle, List.nil_append] using adversaryTable
    rw [nextTable, verifierStartTable, List.map_append]
  rw [List.map_append, scheduler_native_prefix_cursor_append]
  cases verifierPrior with
  | nil => exact (priorNonempty rfl).elim
  | cons head rest =>
      rcases head with ⟨answerInput, answer⟩
      simp only [List.map_cons]
      rw [scheduler_native_prefix_cursor_cons_congr_of_seek_eq transitionFuel
        (schedulerNativePrefixCursor transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (prefixes.adversary.freshQueries.map Prod.snd))
        (fullRootVerifierCursor configuration sample.1
          prefixes.adversaryValue prefixes.adversary.finalState
          prefixes.adversary.finalCoherent) answer (rest.map Prod.snd) boundary]
      unfold fullRootVerifierCursor
      dsimp only [verifierCut, exactCompilerRootSourceAnchoredCut,
        SourceAnchoredMachineCut.ofProjectedPrefix] at localCursor
      exact localCursor

#print axioms projected_fresh_returned_trace_start_coherent
#print axioms source_anchored_machine_cut_native_cursor_after_prefix
#print axioms scheduler_native_prefix_cursor_cons_congr_of_seek_eq
#print axioms scheduler_native_prefix_records_cons_congr_of_seek_eq
#print axioms append_eq_append_prefix_split
#print axioms exact_compiler_alignment_actor_phase_split
#print axioms exact_compiler_alignment_selected_coordinate_phase_split
#print axioms exact_compiler_adversary_boundary_seek_eq_verifier
#print axioms exact_compiler_root_cursor_after_adversary_prefix
#print axioms exact_compiler_root_cursor_after_nonempty_verifier_prefix

end

end AspisK1.V7Tag73SourceAnchoredNativeCursorFactorization
