import AspisFormal.K1.V7Tag73ExactCompilerFinalWorkTraceOccurrence

/-!
# Root origin of the pre-final Tag-73 transcript digest

The selected final-work input serializes the digest produced by the immediately
preceding `final256` absorption.  This module exposes that literal lookup and
then reflects it to the first-creation record in the exact root trace.  The
result is the source fact needed to combine adversary-anchor chronology with
pre-q16 semantic commitment.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFinal256DigestRootOrigin

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The deployed pre-final prefix with the final-256 absorption removed. -/
def prefixAfterC2BeforeFinal256 (messages : Messages) : List MachineEvent :=
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
   challengeEvent messages (.alpha 0)]

theorem prefix_before_final_work_final256_split (messages : Messages) :
    prefixAfterC2BeforeFinalWork messages =
      prefixAfterC2BeforeFinal256 messages ++
        [.absorb (.final256 messages.finalValues)] := by
  simp [prefixAfterC2BeforeFinalWork, prefixAfterC2BeforeFinal256]

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
        obtain ⟨middle, prefixRun, suffixRun⟩ := (ih next).mp tailRun
        exact ⟨middle, Option.bind_eq_some_iff.mpr
          ⟨next, eventRun, prefixRun⟩, suffixRun⟩
      · rintro ⟨middle, prefixRun, suffixRun⟩
        obtain ⟨next, eventRun, tailRun⟩ :=
          Option.bind_eq_some_iff.mp prefixRun
        exact Option.bind_eq_some_iff.mpr
          ⟨next, eventRun, (ih next).mpr ⟨middle, tailRun, suffixRun⟩⟩

/-- The exact accepted execution exposes both the final-256 lookup and the
subsequent final-work lookup.  Hence the state prefix of the latter is
literally the answer of the former. -/
theorem exact_operational_final256_and_work_lookups
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
    ∃ (beforeFinal256 : EvalState) (prefinalDigest workAnswer : Digest256),
      tableLookup (exactOperationalTable input)
          (bytes beforeFinal256.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
                (exactOperationalTape input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape input).messages.finalValues).data) =
        some prefinalDigest ∧
      tableLookup (exactOperationalTable input)
          (bytes prefinalDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.finalGrinding.selected) =
        some workAnswer ∧
      FinalWork34Accepted workAnswer := by
  have strict := input.package.root.fixedRoot.base.strictRefinement
  have refined := (checked_refinement_is_well_formed
    (exactOperationalTable input) exactDeterministicDecoders
    (exactOperationalTape input) (exactOperationalRawTrace input) strict).1
  rw [refine] at refined
  obtain ⟨prefixState, prefixRun, refined⟩ :=
    Option.bind_eq_some_iff.mp refined
  obtain ⟨afterQ16, _q16Run, refined⟩ := Option.bind_eq_some_iff.mp refined
  obtain ⟨finalState, _finalRun, _rawRun⟩ :=
    Option.bind_eq_some_iff.mp refined
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
  obtain ⟨beforeFinalWork, beforeFinalRun, suffixRun⟩ :=
    (run_machine_events_append_iff
      (exactOperationalTable input)
      (prefixAfterC2BeforeFinalWork (exactOperationalTape input).messages)
      [.grind .final (exactOperationalTape input).messages.finalGrinding,
       .check .finalWork,
       .absorb (.finalNonce
        (exactOperationalTape input).messages.finalGrinding.selected)]
      afterC2 prefixState).mp remainingRun
  rw [prefix_before_final_work_final256_split] at beforeFinalRun
  obtain ⟨beforeFinal256, beforeFinal256Run, final256Run⟩ :=
    (run_machine_events_append_iff
      (exactOperationalTable input)
      (prefixAfterC2BeforeFinal256 (exactOperationalTape input).messages)
      [.absorb (.final256 (exactOperationalTape input).messages.finalValues)]
      afterC2 beforeFinalWork).mp beforeFinalRun
  simp only [runMachineEvents] at final256Run
  obtain ⟨afterFinal256, absorbRun, final256Done⟩ :=
    Option.bind_eq_some_iff.mp final256Run
  have afterFinal256Exact : afterFinal256 = beforeFinalWork := by
    simpa [runMachineEvents] using Option.some.inj final256Done
  subst afterFinal256
  have final256Lookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) beforeFinal256 beforeFinalWork
      (.final256 (exactOperationalTape input).messages.finalValues) absorbRun
  simp only [runMachineEvents] at suffixRun
  obtain ⟨afterGrind, grindRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  obtain ⟨afterCheck, checkRun, _suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  have afterCheckExact : afterCheck = afterGrind := by
    simpa [runMachineEvent] using (Option.some.inj checkRun).symm
  subst afterCheck
  obtain ⟨workAnswer, workLookup, workAccepted⟩ :=
    run_grinding_choice_exposes_selected_lookup
      (exactOperationalTable input) beforeFinalWork afterGrind .final
      (exactOperationalTape input).messages.finalGrinding grindRun
  exact ⟨beforeFinal256, beforeFinalWork.digest, workAnswer,
    final256Lookup, workLookup, workAccepted⟩

/-- The final-256 digest has a literal first-creation record in the exact root
trace. -/
theorem exact_operational_prefinal_digest_has_root_record
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
    ∃ actor producerInput prefinalDigest,
      (.machineFresh actor producerInput prefinalDigest :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root ∧
      HasLiteralStatePrefix prefinalDigest
        (bytes prefinalDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected) := by
  obtain ⟨beforeFinal256, prefinalDigest, workAnswer, final256Lookup,
      _workLookup, _workAccepted⟩ :=
    exact_operational_final256_and_work_lookups input
  obtain ⟨actor, rootMember⟩ := exact_final_table_lookup_has_root_record input
    (bytes beforeFinal256.digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape input).messages.finalValues).data)
    prefinalDigest final256Lookup
  refine ⟨actor,
    bytes beforeFinal256.digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape input).messages.finalValues).data,
    prefinalDigest, rootMember, ?_⟩
  unfold HasLiteralStatePrefix
  simpa using
    (List.take_append_length
      (l₁ := bytes prefinalDigest)
      (l₂ := [domGrind] ++
        bytes (exactOperationalTape input).messages.finalGrinding.selected)).symm

#print axioms prefix_before_final_work_final256_split
#print axioms exact_operational_final256_and_work_lookups
#print axioms exact_operational_prefinal_digest_has_root_record

end

end AspisK1.V7Tag73ExactFinal256DigestRootOrigin
