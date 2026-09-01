import AspisFormal.K1.V7Tag73ExactCompilerQ16TraceOccurrence
import AspisFormal.K1.V7Tag73FinalWorkDigestProbability

/-!
# Exact compiler occurrence of the accepted final-work pair

The strict source refinement executes the final 34-bit work check and then
absorbs the selected nonce before q16 begins.  This module isolates those last
three pre-q16 events, exposes both literal fixed-table lookups, and transports
their first creations into the actual result-carrying compiler trace.

This is deliberately an occurrence theorem.  It does not yet choose the
earliest of the two coordinates or prove that the exposure-indexed causal q16
controller routes the complete accepted forest; those are the next source
cover steps.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerQ16TraceOccurrence
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73FinalWorkDigestProbability

noncomputable section

/-! ## Exact final-work suffix -/

/-- The deployed pre-q16 event list with only the final grind/check/absorb
triple removed. -/
def prefixAfterC2BeforeFinalWork (messages : Messages) : List MachineEvent :=
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
  [.absorb (.relationRound 0 (messages.relationSent 0)),
   .grind .fold messages.foldGrinding,
   .check .foldWork,
   .absorb (.foldNonce messages.foldGrinding.selected),
   challengeEvent messages (.alpha 0),
   .absorb (.final256 messages.finalValues)]

theorem prefix_after_c2_final_work_split (messages : Messages) :
    prefixAfterC2 messages =
      prefixAfterC2BeforeFinalWork messages ++
        [.grind .final messages.finalGrinding,
         .check .finalWork,
         .absorb (.finalNonce messages.finalGrinding.selected)] := by
  simp [prefixAfterC2, prefixAfterC2BeforeFinalWork]

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

/-! ## Primitive lookup consequences -/

/-- A successful strict grinding choice exposes the selected nonce's literal
lookup and its stage-local work predicate.  Earlier probes do not advance the
digest. -/
theorem run_grinding_choice_exposes_selected_lookup
    (table : FixedOracleTable) (state next : EvalState)
    (stage : WorkStage) (choice : GrindingChoice stage)
    (run : runGrindingChoice table state stage choice = some next) :
    ∃ output,
      tableLookup table
          (bytes state.digest ++ [domGrind] ++ bytes choice.selected) =
        some output ∧
      workDigestAccepted stage output = true := by
  rw [runGrindingChoice] at run
  obtain ⟨queried, probesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨selectedPair, selectedRun, run⟩ :=
    Option.bind_eq_some_iff.mp run
  rcases selectedPair with ⟨output, afterSelected⟩
  by_cases accepted : workDigestAccepted stage output = true
  · have probesDigest := grinding_probes_do_not_advance table stage
      choice.probesBeforeSelected state queried probesRun
    have selectedLookup : tableLookup table
        (bytes queried.digest ++ [domGrind] ++ bytes choice.selected) =
          some output := by
      simpa only [RawQueryRole.input] using
        (query_step_appends_one table queried afterSelected
          (.grind stage choice.selected) output selectedRun).1
    rw [probesDigest] at selectedLookup
    exact ⟨output, selectedLookup, accepted⟩
  · simp [accepted] at run

/-- Every successful absorb exposes its literal input and the next transcript
digest returned by that lookup. -/
theorem absorb_step_exposes_literal_lookup
    (table : FixedOracleTable) (state next : EvalState) (payload : Payload)
    (run : absorbStep table state payload = some next) :
    tableLookup table
        (bytes state.digest ++ [domAbsorb, payload.label] ++ payload.data) =
      some next.digest := by
  rw [absorbStep] at run
  obtain ⟨pair, queryRun, finalRun⟩ := Option.bind_eq_some_iff.mp run
  rcases pair with ⟨output, stepped⟩
  have steppedExact : stepped = next := by
    simpa only [pure, Option.some.injEq] using finalRun
  subst stepped
  obtain ⟨lookup, _calls, digestExact⟩ := query_step_appends_one table state
    next (.absorb payload) output queryRun
  have outputExact : output = next.digest := by
    simpa only [RawQueryRole.nextDigest] using digestExact.symm
  subst output
  simpa only [RawQueryRole.input] using lookup

/-! ## Strict accepted-source pair -/

/-- The exact accepted source run supplies one 34-bit successful work digest
and the following nonce-absorb answer.  The latter is exactly the q16 base in
the returned deterministic trace. -/
theorem exact_operational_final_work_pair_lookups
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
    ∃ (digest workAnswer q16Base : Digest256),
      tableLookup (exactOperationalTable input)
          (bytes digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected) =
        some workAnswer ∧
      FinalWork34Accepted workAnswer ∧
      tableLookup (exactOperationalTable input)
          (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected) =
        some q16Base ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest := by
  have strict := input.package.root.fixedRoot.base.strictRefinement
  have refined := (checked_refinement_is_well_formed
    (exactOperationalTable input) exactDeterministicDecoders
    (exactOperationalTape input) (exactOperationalRawTrace input) strict).1
  rw [refine] at refined
  obtain ⟨prefixState, prefixRun, refined⟩ :=
    Option.bind_eq_some_iff.mp refined
  obtain ⟨afterQ16, _q16Run, refined⟩ :=
    Option.bind_eq_some_iff.mp refined
  obtain ⟨finalState, _finalRun, rawRun⟩ :=
    Option.bind_eq_some_iff.mp refined
  have rawExact := Option.some.inj rawRun
  have q16BaseExact : prefixState.digest =
      (exactOperationalRawTrace input).q16BaseDigest := by
    simpa using congrArg InteractiveRawTrace.q16BaseDigest rawExact
  rw [runPrefix] at prefixRun
  obtain ⟨beforeC1, _beforeC1Run, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c1Pair, _c1SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c1Pair with ⟨c1Salt, withC1SaltQuery⟩
  obtain ⟨afterC1, _c1AbsorbRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨afterPhaseChallenges, _phaseRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c2Pair, _c2SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c2Pair with ⟨c2Salt, withC2SaltQuery⟩
  obtain ⟨afterC2, _c2AbsorbRun, remainingRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rw [prefix_after_c2_final_work_split] at remainingRun
  obtain ⟨beforeFinalWork, _beforeFinalRun, suffixRun⟩ :=
    (run_machine_events_append_iff
      (exactOperationalTable input)
      (prefixAfterC2BeforeFinalWork (exactOperationalTape input).messages)
      [.grind .final (exactOperationalTape input).messages.finalGrinding,
       .check .finalWork,
       .absorb (.finalNonce
        (exactOperationalTape input).messages.finalGrinding.selected)]
      afterC2 prefixState).mp remainingRun
  simp only [runMachineEvents] at suffixRun
  obtain ⟨afterGrind, grindRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  obtain ⟨afterCheck, checkRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  have afterCheckExact : afterCheck = afterGrind := by
    simpa [runMachineEvent] using (Option.some.inj checkRun).symm
  subst afterCheck
  obtain ⟨afterAbsorb, absorbRun, finalRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  have afterAbsorbExact : afterAbsorb = prefixState := by
    simpa [runMachineEvents] using Option.some.inj finalRun
  subst afterAbsorb
  obtain ⟨workAnswer, workLookup, workAccepted⟩ :=
    run_grinding_choice_exposes_selected_lookup
      (exactOperationalTable input) beforeFinalWork afterGrind .final
      (exactOperationalTape input).messages.finalGrinding grindRun
  have stableDigest : afterGrind.digest = beforeFinalWork.digest :=
    grinding_choice_does_not_advance (exactOperationalTable input)
      beforeFinalWork afterGrind .final
      (exactOperationalTape input).messages.finalGrinding grindRun
  have absorbLookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) afterGrind prefixState
    (.finalNonce
      (exactOperationalTape input).messages.finalGrinding.selected) absorbRun
  rw [stableDigest] at absorbLookup
  refine ⟨beforeFinalWork.digest, workAnswer, prefixState.digest,
    workLookup, ?_, ?_, q16BaseExact⟩
  · exact workAccepted
  · simpa [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using absorbLookup

/-! ## Literal first creations in the compiler trace -/

theorem exact_compiler_full_trace_contains_final_work_pair_fresh
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
    ∃ (digest : Digest256) (workActor : QueryActor)
        (workAnswer : Digest256) (absorbActor : QueryActor)
        (q16Base : Digest256),
      FinalWork34Accepted workAnswer ∧
      (.machineFresh workActor
          (bytes digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected)
          workAnswer : UnifiedExposureRecord) ∈
        (runExactPlainRom transitionFuel configuration sample).trace ∧
      (.machineFresh absorbActor
          (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected)
          q16Base : UnifiedExposureRecord) ∈
        (runExactPlainRom transitionFuel configuration sample).trace ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest := by
  obtain ⟨digest, workAnswer, q16Base, workLookup, workAccepted,
      absorbLookup, q16BaseExact⟩ :=
    exact_operational_final_work_pair_lookups input
  obtain ⟨workActor, workRootMember⟩ :=
    exact_final_table_lookup_has_root_record input _ workAnswer workLookup
  obtain ⟨absorbActor, absorbRootMember⟩ :=
    exact_final_table_lookup_has_root_record input _ q16Base absorbLookup
  refine ⟨digest, workActor, workAnswer, absorbActor, q16Base, workAccepted,
    ?_, ?_, q16BaseExact⟩
  · rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    exact List.mem_append_left _ workRootMember
  · rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    exact List.mem_append_left _ absorbRootMember

/-- Consequently the exhaustive native target scan pauses at both members of
the literal final-work pair, regardless of whether the adversary or verifier
first created either table entry. -/
theorem exact_compiler_full_final_work_pair_scans_paused
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
    ∃ (digest workAnswer q16Base : Digest256),
      FinalWork34Accepted workAnswer ∧
      (∃ pause : SchedulerNativeFreshPause
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)
          (bytes digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected),
        exactCompilerFullTargetScan input
            (bytes digest ++ [domGrind] ++
              bytes (exactOperationalTape input).messages.finalGrinding.selected) =
          .paused pause) ∧
      (∃ pause : SchedulerNativeFreshPause
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)
          (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected),
        exactCompilerFullTargetScan input
            (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++
              bytes (exactOperationalTape input).messages.finalGrinding.selected) =
          .paused pause) ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest := by
  obtain ⟨digest, workActor, workAnswer, absorbActor, q16Base, accepted,
      workMember, absorbMember, q16BaseExact⟩ :=
    exact_compiler_full_trace_contains_final_work_pair_fresh input
  obtain ⟨workPause, workPaused⟩ :=
    exact_compiler_full_target_scan_paused_of_trace_mem input _ workActor
      workAnswer workMember
  obtain ⟨absorbPause, absorbPaused⟩ :=
    exact_compiler_full_target_scan_paused_of_trace_mem input _ absorbActor
      q16Base absorbMember
  exact ⟨digest, workAnswer, q16Base, accepted,
    ⟨workPause, workPaused⟩, ⟨absorbPause, absorbPaused⟩, q16BaseExact⟩

#print axioms prefix_after_c2_final_work_split
#print axioms run_grinding_choice_exposes_selected_lookup
#print axioms absorb_step_exposes_literal_lookup
#print axioms exact_operational_final_work_pair_lookups
#print axioms exact_compiler_full_trace_contains_final_work_pair_fresh
#print axioms exact_compiler_full_final_work_pair_scans_paused

end

end AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
