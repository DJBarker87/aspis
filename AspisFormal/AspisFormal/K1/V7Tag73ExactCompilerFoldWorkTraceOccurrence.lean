import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
import AspisFormal.K1.V7Tag73ExactCompilerFinalWorkTraceOccurrence

/-!
# Exact compiler occurrence of the accepted fold-work answer

The strict accepted Tag-73 evaluator executes the selected 31-bit fold-work
probe before absorbing the fold nonce and sampling alpha zero.  This module
cuts that literal event from the accepted post-C2 run and transports its
lookup into the result-carrying compiler trace.  It does not infer a logical
role from raw SHA bytes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerFoldWorkTraceOccurrence

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

private theorem run_machine_events_append_iff
    (table : FixedOracleTable) (first second : List MachineEvent)
    (state final : EvalState) :
    runMachineEvents table (first ++ second) state = some final ↔
      ∃ middle,
        runMachineEvents table first state = some middle ∧
        runMachineEvents table second middle = some final := by
  induction first generalizing state with
  | nil => simp [runMachineEvents]
  | cons event rest ih =>
      simp only [List.cons_append, runMachineEvents]
      constructor
      · intro run
        obtain ⟨next, eventRun, tailRun⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨middle, restRun, secondRun⟩ :=
          (ih (state := next)).mp tailRun
        exact ⟨middle,
          Option.bind_eq_some_iff.mpr ⟨next, eventRun, restRun⟩,
          secondRun⟩
      · rintro ⟨middle, firstRun, secondRun⟩
        obtain ⟨next, eventRun, restRun⟩ :=
          Option.bind_eq_some_iff.mp firstRun
        exact Option.bind_eq_some_iff.mpr
          ⟨next, eventRun, (ih (state := next)).mpr
            ⟨middle, restRun, secondRun⟩⟩

/-- Accepted post-C2 events strictly before the fold-work grind. -/
def prefixAfterC2BeforeFoldWork (messages : Messages) : List MachineEvent :=
  [.absorb .constraintRegistry,
   .absorb .helperSum,
   challengeEvent messages .theta] ++
  (List.ofFn fun coordinate : Fin 10 =>
    challengeEvent messages (.zerocheckPoint coordinate)) ++
  [challengeEvent messages .mu,
   .absorb (.initialMaskClaim messages.initialClaim),
   challengeEvent messages .eta] ++
  semanticEvents messages ++
  [.absorb (.pointClaims messages.pointClaims),
   .check .semanticTerminal,
   .grind .batch messages.batchGrinding,
   .check .batchWork,
   .absorb (.batchNonce messages.batchGrinding.selected),
   challengeEvent messages .gamma,
   .absorb (.inactiveClaim messages.inactiveClaim),
   challengeEvent messages .kappa] ++
  oodEvents messages ++
  [.absorb (.relationRound 0 (messages.relationSent 0))]

/-- The complete literal suffix beginning at the selected fold-work probe. -/
def prefixAfterC2FromFoldWork (messages : Messages) : List MachineEvent :=
  [.grind .fold messages.foldGrinding,
   .check .foldWork,
   .absorb (.foldNonce messages.foldGrinding.selected),
   challengeEvent messages (.alpha 0),
   .absorb (.final256 messages.finalValues),
   .grind .final messages.finalGrinding,
   .check .finalWork,
   .absorb (.finalNonce messages.finalGrinding.selected)]

theorem prefix_after_c2_fold_work_split (messages : Messages) :
    prefixAfterC2 messages =
      prefixAfterC2BeforeFoldWork messages ++
        prefixAfterC2FromFoldWork messages := by
  simp [prefixAfterC2, prefixAfterC2BeforeFoldWork,
    prefixAfterC2FromFoldWork]

/-- Strict source acceptance supplies the selected fold-work table answer and
its exact 31-bit predicate at the literal deployed input. -/
theorem exact_operational_fold_work_lookup
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (digest workAnswer : Digest256),
      tableLookup (exactOperationalTable input)
          (bytes digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected) =
        some workAnswer ∧
      FoldWork31Accepted workAnswer := by
  have strict := input.package.root.fixedRoot.base.strictRefinement
  have refined := (checked_refinement_is_well_formed
    (exactOperationalTable input) exactDeterministicDecoders
    (exactOperationalTape input) (exactOperationalRawTrace input) strict).1
  rw [refine] at refined
  obtain ⟨prefixState, prefixRun, _refined⟩ :=
    Option.bind_eq_some_iff.mp refined
  rw [runPrefix] at prefixRun
  obtain ⟨beforeC1, _beforeC1Run, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c1Pair, _c1SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c1Pair with ⟨_c1Salt, _withC1SaltQuery⟩
  obtain ⟨afterC1, _c1AbsorbRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨afterPhaseChallenges, _phaseRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c2Pair, _c2SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c2Pair with ⟨_c2Salt, _withC2SaltQuery⟩
  obtain ⟨afterC2, _c2AbsorbRun, remainingRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rw [prefix_after_c2_fold_work_split] at remainingRun
  obtain ⟨beforeFoldWork, _beforeFoldRun, suffixRun⟩ :=
    (run_machine_events_append_iff
      (exactOperationalTable input)
      (prefixAfterC2BeforeFoldWork (exactOperationalTape input).messages)
      (prefixAfterC2FromFoldWork (exactOperationalTape input).messages)
      afterC2 prefixState).mp remainingRun
  simp only [prefixAfterC2FromFoldWork, runMachineEvents] at suffixRun
  obtain ⟨afterFoldGrind, foldGrindRun, _suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  obtain ⟨workAnswer, workLookup, workAccepted⟩ :=
    run_grinding_choice_exposes_selected_lookup
      (exactOperationalTable input) beforeFoldWork afterFoldGrind .fold
      (exactOperationalTape input).messages.foldGrinding foldGrindRun
  exact ⟨beforeFoldWork.digest, workAnswer, workLookup, workAccepted⟩

/-- The accepted fold-work lookup has a literal actor-tagged first creation in
the compiler trace, including adversary-first cache population. -/
theorem exact_compiler_full_trace_contains_fold_work_fresh
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (digest : Digest256) (actor : QueryActor) (workAnswer : Digest256),
      FoldWork31Accepted workAnswer ∧
      (.machineFresh actor
          (bytes digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          workAnswer : UnifiedExposureRecord) ∈
        (runExactPlainRom transitionFuel configuration sample).trace := by
  obtain ⟨digest, workAnswer, workLookup, workAccepted⟩ :=
    exact_operational_fold_work_lookup input
  obtain ⟨actor, rootMember⟩ :=
    exact_final_table_lookup_has_root_record input _ workAnswer workLookup
  refine ⟨digest, actor, workAnswer, workAccepted, ?_⟩
  rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
    configuration projection fixedInstance sample input.package]
  exact List.mem_append_left _ rootMember

/-- The exhaustive native scan therefore pauses at the exact fold-work input. -/
theorem exact_compiler_full_fold_work_scan_paused
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (digest workAnswer : Digest256),
      FoldWork31Accepted workAnswer ∧
      ∃ pause : SchedulerNativeFreshPause
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)
          (bytes digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected),
        exactCompilerFullTargetScan input
            (bytes digest ++ [domGrind] ++
              bytes (exactOperationalTape input).messages.foldGrinding.selected) =
          .paused pause := by
  obtain ⟨digest, actor, workAnswer, accepted, member⟩ :=
    exact_compiler_full_trace_contains_fold_work_fresh input
  obtain ⟨pause, paused⟩ :=
    exact_compiler_full_target_scan_paused_of_trace_mem input _ actor
      workAnswer member
  exact ⟨digest, workAnswer, accepted, pause, paused⟩

end


#print axioms prefix_after_c2_fold_work_split
#print axioms exact_operational_fold_work_lookup
#print axioms exact_compiler_full_trace_contains_fold_work_fresh
#print axioms exact_compiler_full_fold_work_scan_paused

end AspisK1.V7Tag73ExactCompilerFoldWorkTraceOccurrence
