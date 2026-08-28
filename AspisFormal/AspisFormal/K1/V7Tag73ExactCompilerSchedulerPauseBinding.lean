import AspisFormal.K1.V7Tag73SchedulerNativeTargetPause
import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier

/-!
# Exact-compiler binding for the scheduler-native target pause

This module applies the executable scheduler-native scanner to the two literal
deployed cursors and to the one unified full-256 master tape contained in an
`ExactCompilerSample`.

The root scan is the relevant pre-challenge scan: it contains only the initial
prover and dependent-verifier execution.  The full scan is also retained, so a
successful pause can be related directly to the production result-carrying
scheduler.  In either case the scanner itself decides occurrence versus
absence.  No occurrence, replay, source-equality, or returned-value premise is
added to the state.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73SchedulerNativeTargetPause

noncomputable section

/-! ## Generic occurrence completeness of the executable scan -/

/-- An absent scanner result contains no selected machine-fresh record.  This
is the converse direction needed to derive a pause from an independently
proved source-trace occurrence. -/
theorem scan_scheduler_native_to_input_from_absent_avoids_target
    {globalOracleCalls : Nat} {SchedulerResult : Type}
    (transitionFuel : Nat) (target : ShaInput) :
    ∀ (currentTransitionFuel : Nat)
      (cursor : SchedulerNativeCursor globalOracleCalls SchedulerResult)
      (answers : List Digest256) (run : SchedulerNativeRun SchedulerResult),
      scanSchedulerNativeToInputFrom transitionFuel target
          currentTransitionFuel cursor answers = .absent run →
        ∀ actor answer,
          (.machineFresh actor target answer : UnifiedExposureRecord) ∉
            run.trace := by
  intro currentTransitionFuel cursor answers
  induction answers generalizing currentTransitionFuel cursor with
  | nil =>
      intro run absent actor answer member
      simp [scanSchedulerNativeToInputFrom] at absent
      cases absent
      simp at member
  | cons currentAnswer rest ih =>
      intro run absent actor answer member
      simp only [scanSchedulerNativeToInputFrom] at absent
      split at absent <;> rename_i requestExact
      · rename_i result
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.returned result :
              SchedulerNativeCursor globalOracleCalls SchedulerResult)
            rest = scan at absent
        cases scan with
        | paused pause => contradiction
        | absent tail =>
            cases absent
            simp only [List.mem_cons] at member
            rcases member with head | tailMember
            · cases head
            · exact ih transitionFuel
                (.returned result :
                  SchedulerNativeCursor globalOracleCalls SchedulerResult)
                tail scanExact actor answer tailMember
      · rename_i reason
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed reason :
              SchedulerNativeCursor globalOracleCalls SchedulerResult)
            rest = scan at absent
        cases scan with
        | paused pause => contradiction
        | absent tail =>
            cases absent
            simp only [List.mem_cons] at member
            rcases member with head | tailMember
            · cases head
            · exact ih transitionFuel
                (.failed reason :
                  SchedulerNativeCursor globalOracleCalls SchedulerResult)
                tail scanExact actor answer tailMember
      · generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (.failed .transitionLimit :
              SchedulerNativeCursor globalOracleCalls SchedulerResult)
            rest = scan at absent
        cases scan with
        | paused pause => contradiction
        | absent tail =>
            cases absent
            simp only [List.mem_cons] at member
            rcases member with head | tailMember
            · cases head
            · exact ih transitionFuel
                (.failed .transitionLimit :
                  SchedulerNativeCursor globalOracleCalls SchedulerResult)
                tail scanExact actor answer tailMember
      · rename_i MachineResult limits limitBound requestActor requestState input
          nextProgram remainingFuel coherent totalRoom freshRoom missing
          onReturned
        split at absent
        next input_eq_target => contradiction
        next input_ne_target =>
          let nextCursor :
              SchedulerNativeCursor globalOracleCalls SchedulerResult :=
            .machine limits limitBound requestActor
              (freshQueryState requestActor requestState input currentAnswer)
              (nextProgram currentAnswer) remainingFuel
              (fresh_query_state_preserves_history_total_coherent requestActor
                requestState input currentAnswer coherent) onReturned
          generalize scanExact :
            scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
              nextCursor rest = scan at absent
          cases scan with
          | paused pause => contradiction
          | absent tail =>
              cases absent
              simp only [List.mem_cons] at member
              rcases member with head | tailMember
              · cases head
                exact input_ne_target rfl
              · exact ih transitionFuel nextCursor tail scanExact actor answer
                  tailMember
      · rename_i frozenHistory pairRoom outputInput advanceInput template next
        let nextCursor :
            SchedulerNativeCursor globalOracleCalls SchedulerResult :=
          .forkAdvance frozenHistory pairRoom outputInput advanceInput template
            currentAnswer next
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            nextCursor rest = scan at absent
        cases scan with
        | paused pause => contradiction
        | absent tail =>
            cases absent
            simp only [List.mem_cons] at member
            rcases member with head | tailMember
            · cases head
            · exact ih transitionFuel nextCursor tail scanExact actor answer
                tailMember
      · rename_i frozenHistory pairRoom outputInput advanceInput template
          forkOutput next
        let scheduled : ScheduledForkCoins :=
          { frozenHistory := frozenHistory
            outputInput := outputInput
            advanceInput := advanceInput
            template := template
            forkOutput := forkOutput
            forkAdvance := currentAnswer }
        generalize scanExact :
          scanSchedulerNativeToInputFrom transitionFuel target transitionFuel
            (next scheduled.configuration) rest = scan at absent
        cases scan with
        | paused pause => contradiction
        | absent tail =>
            cases absent
            simp only [List.mem_cons] at member
            rcases member with head | tailMember
            · cases head
            · exact ih transitionFuel (next scheduled.configuration) tail
                scanExact actor answer tailMember

/-- Any selected machine-fresh record in the literal scheduler run forces the
executable scanner to return a pause. -/
theorem scan_scheduler_native_to_input_paused_of_target_mem
    {globalOracleCalls : Nat} {SchedulerResult : Type}
    (transitionFuel : Nat) (target : ShaInput)
    (cursor : SchedulerNativeCursor globalOracleCalls SchedulerResult)
    (answers : List Digest256) (actor : QueryActor) (answer : Digest256)
    (member : (.machineFresh actor target answer : UnifiedExposureRecord) ∈
      (runSchedulerNativeListRun transitionFuel cursor answers).trace) :
    ∃ pause : SchedulerNativeFreshPause globalOracleCalls SchedulerResult
        target,
      scanSchedulerNativeToInput transitionFuel target cursor answers =
        .paused pause := by
  cases scanExact : scanSchedulerNativeToInput transitionFuel target cursor
      answers with
  | paused pause => exact ⟨pause, rfl⟩
  | absent run =>
      have runExact := scan_scheduler_native_to_input_absent_exact
        transitionFuel target cursor answers run scanExact
      have targetAbsent :=
        scan_scheduler_native_to_input_from_absent_avoids_target transitionFuel
          target transitionFuel cursor answers run scanExact actor answer
      exact (targetAbsent (runExact ▸ member)).elim

/-! ## Literal deployed scans -/

/-- Scan the actual initial-only Tag-73 cursor on the actual unified master
tape.  This is the earliest scheduler-level object in the exact compiler that
still contains the adversary and dependent-verifier computation returning the
parsed proof. -/
def exactCompilerRootTargetScan
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) :
    SchedulerNativeTargetScan (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload PUnit) target :=
  scanSchedulerNativeToInput transitionFuel target
    (exactPlainRomRootCursor configuration sample.1)
    (freshAnswerTapeToList sample.2)

/-- Scan the actual result-carrying Tag-73 cursor on the same actual unified
master tape. -/
def exactCompilerFullTargetScan
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) :
    SchedulerNativeTargetScan (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) target :=
  scanSchedulerNativeToInput transitionFuel target
    (exactPlainRomCursor configuration sample.1)
    (freshAnswerTapeToList sample.2)

/-! ## Exact reconstruction -/

/-- Interpreting the root scan reconstructs the literal initial-only
production scheduler, including its terminal and its complete exposure trace.
-/
theorem exact_compiler_root_target_scan_reconstructs_run
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) :
    (exactCompilerRootTargetScan input target).reconstructedRun transitionFuel =
      runExactPlainRomRoot transitionFuel configuration sample := by
  unfold exactCompilerRootTargetScan runExactPlainRomRoot
  rw [run_scheduler_native_eq_list_run]
  exact scan_scheduler_native_to_input_reconstructs_run transitionFuel target
    (exactPlainRomRootCursor configuration sample.1)
    (freshAnswerTapeToList sample.2)

/-- Interpreting the full scan reconstructs the literal result-carrying
production scheduler, including its terminal and its complete exposure trace.
-/
theorem exact_compiler_full_target_scan_reconstructs_run
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) :
    (exactCompilerFullTargetScan input target).reconstructedRun transitionFuel =
      runExactPlainRom transitionFuel configuration sample := by
  unfold exactCompilerFullTargetScan runExactPlainRom
  rw [run_scheduler_native_eq_list_run]
  exact scan_scheduler_native_to_input_reconstructs_run transitionFuel target
    (exactPlainRomCursor configuration sample.1)
    (freshAnswerTapeToList sample.2)

/-- A source-level occurrence in the literal root trace is exactly the one
non-conclusion-shaped fact needed to rule out the scanner's absent branch. -/
theorem exact_compiler_root_target_scan_paused_of_trace_mem
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) (actor : QueryActor) (answer : Digest256)
    (member : (.machineFresh actor target answer : UnifiedExposureRecord) ∈
      (runExactPlainRomRoot transitionFuel configuration sample).trace) :
    ∃ pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload PUnit) target,
      exactCompilerRootTargetScan input target = .paused pause := by
  apply scan_scheduler_native_to_input_paused_of_target_mem transitionFuel
    target (exactPlainRomRootCursor configuration sample.1)
      (freshAnswerTapeToList sample.2) actor answer
  simpa [runExactPlainRomRoot, run_scheduler_native_eq_list_run] using member

/-- The same occurrence-completeness specialization for the result-carrying
production cursor. -/
theorem exact_compiler_full_target_scan_paused_of_trace_mem
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) (actor : QueryActor) (answer : Digest256)
    (member : (.machineFresh actor target answer : UnifiedExposureRecord) ∈
      (runExactPlainRom transitionFuel configuration sample).trace) :
    ∃ pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result) target,
      exactCompilerFullTargetScan input target = .paused pause := by
  apply scan_scheduler_native_to_input_paused_of_target_mem transitionFuel
    target (exactPlainRomCursor configuration sample.1)
      (freshAnswerTapeToList sample.2) actor answer
  simpa [runExactPlainRom, run_scheduler_native_eq_list_run] using member

/-! ## Occurrence and no-occurrence branches -/

/-- If the executable root scan pauses, its saved answer and untouched suffix
are the literal split of the exact compiler master tape. -/
theorem exact_compiler_root_target_pause_master_tape_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (pause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload PUnit) target)
    (found : exactCompilerRootTargetScan input target = .paused pause) :
    freshAnswerTapeToList sample.2 = pause.consumedAnswers ++
      pause.targetAnswer :: pause.remainingAnswers := by
  exact scan_scheduler_native_to_input_paused_answers_exact transitionFuel
    target (exactPlainRomRootCursor configuration sample.1)
      (freshAnswerTapeToList sample.2) pause found

/-- Retained-answer replay of a root pause is the complete deployed root run,
not only a terminal-value agreement. -/
theorem exact_compiler_root_target_pause_resume_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (pause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload PUnit) target)
    (found : exactCompilerRootTargetScan input target = .paused pause) :
    pause.resumeRun transitionFuel =
      runExactPlainRomRoot transitionFuel configuration sample := by
  have reconstructed := exact_compiler_root_target_scan_reconstructs_run
    input target
  rw [found] at reconstructed
  exact reconstructed

/-- An absent root scan contains the complete deployed root run. -/
theorem exact_compiler_root_target_absent_run_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (run : SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload PUnit))
    (absent : exactCompilerRootTargetScan input target = .absent run) :
    run = runExactPlainRomRoot transitionFuel configuration sample := by
  have reconstructed := exact_compiler_root_target_scan_reconstructs_run
    input target
  rw [absent] at reconstructed
  exact reconstructed

/-- On the occurrence branch, supplying the retained actual answer and unread
suffix returns the exact root run and therefore the exact K1.2 runtime. -/
theorem exact_compiler_root_target_pause_returns_exact_k12_runtime
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (pause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload PUnit) target)
    (found : exactCompilerRootTargetScan input target = .paused pause) :
    (pause.resumeRun transitionFuel).terminal =
      .returned (.completed (exactK12Runtime input)
        input.package.root.fixedRoot.base.clientRun) := by
  have reconstructed := exact_compiler_root_target_scan_reconstructs_run
    input target
  rw [found] at reconstructed
  exact (congrArg SchedulerNativeRun.terminal reconstructed).trans
    (by simpa [exactK12Runtime] using
      input.package.root.fixedRoot.base.rootCompleted)

/-- On the no-occurrence branch, the computed absent run is still exactly the
root production run and returns the exact K1.2 runtime. -/
theorem exact_compiler_root_target_absent_returns_exact_k12_runtime
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (run : SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload PUnit))
    (absent : exactCompilerRootTargetScan input target = .absent run) :
    run.terminal = .returned (.completed (exactK12Runtime input)
      input.package.root.fixedRoot.base.clientRun) := by
  have reconstructed := exact_compiler_root_target_scan_reconstructs_run
    input target
  rw [absent] at reconstructed
  exact (congrArg SchedulerNativeRun.terminal reconstructed).trans
    (by simpa [exactK12Runtime] using
      input.package.root.fixedRoot.base.rootCompleted)

/-- If the full scan pauses, the scanner retains the literal split of the
same unified compiler master tape. -/
theorem exact_compiler_full_target_pause_master_tape_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (pause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) target)
    (found : exactCompilerFullTargetScan input target = .paused pause) :
    freshAnswerTapeToList sample.2 = pause.consumedAnswers ++
      pause.targetAnswer :: pause.remainingAnswers := by
  exact scan_scheduler_native_to_input_paused_answers_exact transitionFuel
    target (exactPlainRomCursor configuration sample.1)
      (freshAnswerTapeToList sample.2) pause found

/-- Retained-answer replay of a full pause is the complete deployed
result-carrying run. -/
theorem exact_compiler_full_target_pause_resume_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (pause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) target)
    (found : exactCompilerFullTargetScan input target = .paused pause) :
    pause.resumeRun transitionFuel =
      runExactPlainRom transitionFuel configuration sample := by
  have reconstructed := exact_compiler_full_target_scan_reconstructs_run
    input target
  rw [found] at reconstructed
  exact reconstructed

/-- An absent full scan contains the complete deployed result-carrying run. -/
theorem exact_compiler_full_target_absent_run_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (run : SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (absent : exactCompilerFullTargetScan input target = .absent run) :
    run = runExactPlainRom transitionFuel configuration sample := by
  have reconstructed := exact_compiler_full_target_scan_reconstructs_run
    input target
  rw [absent] at reconstructed
  exact reconstructed

/-- On the occurrence branch of the full result-carrying scheduler, retained
actual replay returns the exact production runtime and client result. -/
theorem exact_compiler_full_target_pause_returns_actual_production_result
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (pause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) target)
    (found : exactCompilerFullTargetScan input target = .paused pause) :
    (pause.resumeRun transitionFuel).terminal =
      .returned (.completed (exactK12Runtime input)
        input.package.root.full.clientRun) := by
  have reconstructed := exact_compiler_full_target_scan_reconstructs_run
    input target
  rw [found] at reconstructed
  exact (congrArg SchedulerNativeRun.terminal reconstructed).trans
    (by simpa [exactK12Runtime] using input.package.root.full.fullCompleted)

/-- On the no-occurrence branch of the full scheduler, the absent result is
the exact production result rather than a separately modeled execution. -/
theorem exact_compiler_full_target_absent_returns_actual_production_result
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput)
    (run : SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (absent : exactCompilerFullTargetScan input target = .absent run) :
    run.terminal = .returned (.completed (exactK12Runtime input)
      input.package.root.full.clientRun) := by
  have reconstructed := exact_compiler_full_target_scan_reconstructs_run
    input target
  rw [absent] at reconstructed
  exact (congrArg SchedulerNativeRun.terminal reconstructed).trans
    (by simpa [exactK12Runtime] using input.package.root.full.fullCompleted)

/-! ## Total executable dichotomy -/

/-- The actual root scan unconditionally computes either an exact pre-target
pause or an exact absent run.  Both branches are tied to the returned parsed
proof runtime already consumed by K1.2--K1.5. -/
theorem exact_compiler_root_target_pause_or_absent
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) :
    (∃ pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload PUnit) target,
      exactCompilerRootTargetScan input target = .paused pause ∧
      freshAnswerTapeToList sample.2 = pause.consumedAnswers ++
        pause.targetAnswer :: pause.remainingAnswers ∧
      (pause.resumeRun transitionFuel).terminal =
        .returned (.completed (exactK12Runtime input)
          input.package.root.fixedRoot.base.clientRun)) ∨
    (∃ run : SchedulerNativeRun
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload PUnit),
      exactCompilerRootTargetScan input target = .absent run ∧
      run = runExactPlainRomRoot transitionFuel configuration sample ∧
      run.terminal = .returned (.completed (exactK12Runtime input)
        input.package.root.fixedRoot.base.clientRun)) := by
  cases scanExact : exactCompilerRootTargetScan input target with
  | paused pause =>
      exact Or.inl ⟨pause, rfl,
        exact_compiler_root_target_pause_master_tape_exact input target pause
          scanExact,
        exact_compiler_root_target_pause_returns_exact_k12_runtime input target
          pause scanExact⟩
  | absent run =>
      have runExact : run =
          runExactPlainRomRoot transitionFuel configuration sample := by
        rw [runExactPlainRomRoot, run_scheduler_native_eq_list_run]
        exact scan_scheduler_native_to_input_absent_exact transitionFuel target
          (exactPlainRomRootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) run scanExact
      exact Or.inr ⟨run, rfl, runExact,
        exact_compiler_root_target_absent_returns_exact_k12_runtime input target
          run scanExact⟩

/-- The actual full scheduler scan also computes an unconditional exact
pause/absence dichotomy.  In the occurrence branch it exposes the literal
master-tape split; in both branches it returns the actual production result.
-/
theorem exact_compiler_full_target_pause_or_absent
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) :
    (∃ pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result) target,
      exactCompilerFullTargetScan input target = .paused pause ∧
      freshAnswerTapeToList sample.2 = pause.consumedAnswers ++
        pause.targetAnswer :: pause.remainingAnswers ∧
      pause.resumeRun transitionFuel =
        runExactPlainRom transitionFuel configuration sample ∧
      (pause.resumeRun transitionFuel).terminal =
        .returned (.completed (exactK12Runtime input)
          input.package.root.full.clientRun)) ∨
    (∃ run : SchedulerNativeRun
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result),
      exactCompilerFullTargetScan input target = .absent run ∧
      run = runExactPlainRom transitionFuel configuration sample ∧
      run.terminal = .returned (.completed (exactK12Runtime input)
        input.package.root.full.clientRun)) := by
  cases scanExact : exactCompilerFullTargetScan input target with
  | paused pause =>
      exact Or.inl ⟨pause, rfl,
        exact_compiler_full_target_pause_master_tape_exact input target pause
          scanExact,
        exact_compiler_full_target_pause_resume_exact input target pause
          scanExact,
        exact_compiler_full_target_pause_returns_actual_production_result input
          target pause scanExact⟩
  | absent run =>
      exact Or.inr ⟨run, rfl,
        exact_compiler_full_target_absent_run_exact input target run scanExact,
        exact_compiler_full_target_absent_returns_actual_production_result input
          target run scanExact⟩

#print axioms scan_scheduler_native_to_input_from_absent_avoids_target
#print axioms scan_scheduler_native_to_input_paused_of_target_mem
#print axioms exact_compiler_root_target_scan_reconstructs_run
#print axioms exact_compiler_full_target_scan_reconstructs_run
#print axioms exact_compiler_root_target_scan_paused_of_trace_mem
#print axioms exact_compiler_full_target_scan_paused_of_trace_mem
#print axioms exact_compiler_root_target_pause_master_tape_exact
#print axioms exact_compiler_root_target_pause_resume_exact
#print axioms exact_compiler_root_target_absent_run_exact
#print axioms exact_compiler_root_target_pause_returns_exact_k12_runtime
#print axioms exact_compiler_root_target_absent_returns_exact_k12_runtime
#print axioms exact_compiler_full_target_pause_master_tape_exact
#print axioms exact_compiler_full_target_pause_resume_exact
#print axioms exact_compiler_full_target_absent_run_exact
#print axioms exact_compiler_full_target_pause_returns_actual_production_result
#print axioms exact_compiler_full_target_absent_returns_actual_production_result
#print axioms exact_compiler_root_target_pause_or_absent
#print axioms exact_compiler_full_target_pause_or_absent

end

end AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
