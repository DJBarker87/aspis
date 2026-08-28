import AspisFormal.K1.V7Tag73SchedulerNativeTargetPause
import AspisFormal.K1.V7Tag73VariablePrefixGammaSampler

/-!
# Scheduler-native counterfactual replay of the Tag-73 gamma sampler

This module runs the variable-prefix gamma sampler directly inside the
result-carrying scheduler.  It begins at the executable first-target scan from
`V7Tag73SchedulerNativeTargetPause`.  At each sampler coordinate it replaces
only the selected fresh answer, then scans the ordinary scheduler over the
untouched master-tape suffix until the dynamically computed next input is
reached.  Thus arbitrary machine and atomic-fork activity between gamma
queries is executed by the production scheduler rather than skipped.

The driver stops at the first successful `decodeNonzeroPrefix`; unread duplex
coordinates and the unread master-tape suffix are not executed.  The absent
case is the exact run already computed by the exhaustive first-target scan.
No cross-gamma coherence or source-level identification of the supplied tape
is assumed here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeGammaReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisV5ComponentCQM31TowerExact

noncomputable section

universe u

structure SchedulerNativeGammaNuisance where
  initialDigest : Digest256

inductive SchedulerNativeGammaQueryKind where
  | output
  | advance
  deriving DecidableEq

inductive SchedulerNativeGammaReplayFailure where
  | samplerTapeExhausted
  | expectedQueryAbsent (kind : SchedulerNativeGammaQueryKind)
  | queryActorMismatch (kind : SchedulerNativeGammaQueryKind)
  | decodedValueInvalid
  | gammaMismatch
  deriving DecidableEq

def gammaOutputInput (digest : Digest256) : ShaInput :=
  bytes digest ++ [domSqueeze]

def gammaAdvanceInput (digest : Digest256) : ShaInput :=
  bytes digest ++ [domAdvance]

def gammaDuplexPairs (tape : TotalGammaDuplexTape) :
    List (Digest256 × Digest256) :=
  (List.ofFn tape.1).zip (List.ofFn tape.2)

/-- Observable result of a scheduler-native counterfactual replay.  A
successful occurrence has both gamma fields present; the exhaustive absent
branch has both absent. -/
structure SchedulerNativeGammaResponse (Result : Type u) where
  run : SchedulerNativeRun Result
  consumedBlocks : Nat
  returnedGamma : Option QM31Exact
  decodedBytes : Option Qm31Bytes
  remainingAnswers : List Digest256

/-- Internal occurrence result retaining the kernel-checked decoding
equality. -/
structure DecodedSchedulerNativeGammaResponse (Result : Type u) where
  response : SchedulerNativeGammaResponse Result
  decoded : OrdinaryPrefixDecode
  value : QM31Exact
  valueExact : decodeTagQM31ExactLE decoded.value = some value
  responseBytesExact : response.decodedBytes = some decoded.value

def machineFreshRecord
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (answer : Digest256) : UnifiedExposureRecord :=
  .machineFresh pause.actor pause.input answer

def prependDecodedTrace {Result : Type u}
    (tracePrefix : List UnifiedExposureRecord)
    (decoded : DecodedSchedulerNativeGammaResponse Result) :
    DecodedSchedulerNativeGammaResponse Result :=
  { decoded with
    response :=
      { decoded.response with
        run :=
          { terminal := decoded.response.run.terminal
            trace := tracePrefix ++ decoded.response.run.trace } } }

/-- Execute the sampler from a pause at its next output query.  The two scans
in each iteration consume arbitrary intervening scheduler coordinates from
the retained master-tape suffix.  Only the selected output and advance fresh
answers are replaced by the corresponding fixed duplex coordinates. -/
def runSchedulerNativeGammaPrefix
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (expectedActor : QueryActor) :
    (pairs : List (Digest256 × Digest256)) →
      (consumedBlocks : Nat) → (digest : Digest256) →
      (outputs : List Digest256) →
      SchedulerNativeFreshPause globalOracleCalls Result
        (gammaOutputInput digest) →
      Except SchedulerNativeGammaReplayFailure
        (DecodedSchedulerNativeGammaResponse Result)
  | [], _, _, _, _ => .error .samplerTapeExhausted
  | (output, advanced) :: rest, consumedBlocks, digest, outputs, outputPause =>
      if _outputActor : outputPause.actor = expectedActor then
        let afterOutputCursor := outputPause.resumeCursorWith output
        let afterOutputAnswers := outputPause.remainingAnswers
        match _advanceScan : scanSchedulerNativeToInput transitionFuel
            (gammaAdvanceInput digest) afterOutputCursor afterOutputAnswers with
        | .absent _ => .error (.expectedQueryAbsent .advance)
        | .paused advancePause =>
            if _advanceActor : advancePause.actor = expectedActor then
              let afterAdvanceCursor := advancePause.resumeCursorWith advanced
              let afterAdvanceAnswers := advancePause.remainingAnswers
              let nextOutputs := outputs ++ [output]
              let tracePrefix := outputPause.consumedTrace ++
                machineFreshRecord outputPause output ::
                advancePause.consumedTrace ++
                [machineFreshRecord advancePause advanced]
              match _decodedRun : decodeNonzeroPrefix 3 nextOutputs with
              | some decoded =>
                  match valueRun : decodeTagQM31ExactLE decoded.value with
                  | none => .error .decodedValueInvalid
                  | some value =>
                      let tail := runSchedulerNativeListRun transitionFuel
                        afterAdvanceCursor afterAdvanceAnswers
                      .ok
                        { response :=
                            { run :=
                                { terminal := tail.terminal
                                  trace := tracePrefix ++ tail.trace }
                              consumedBlocks := consumedBlocks + 1
                              returnedGamma := some value
                              decodedBytes := some decoded.value
                              remainingAnswers := afterAdvanceAnswers }
                          decoded := decoded
                          value := value
                          valueExact := valueRun
                          responseBytesExact := rfl }
              | none =>
                  match _outputScan : scanSchedulerNativeToInput transitionFuel
                      (gammaOutputInput advanced) afterAdvanceCursor
                      afterAdvanceAnswers with
                  | .absent _ => .error (.expectedQueryAbsent .output)
                  | .paused nextOutputPause =>
                      (runSchedulerNativeGammaPrefix transitionFuel
                        expectedActor rest (consumedBlocks + 1) advanced
                        nextOutputs nextOutputPause).map
                          (prependDecodedTrace tracePrefix)
            else
              .error (.queryActorMismatch .advance)
      else
        .error (.queryActorMismatch .output)

/-- Occurrence replay.  The complete possible duplex tape is fixed before
the supplied gamma, while execution consumes only its successful prefix. -/
def replaySchedulerNativeOccurrenceAtGamma
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest))
    (tape : TotalGammaDuplexTape) (gamma : NonzeroQM31Exact) :
    Except SchedulerNativeGammaReplayFailure
      (SchedulerNativeGammaResponse Result) :=
  match runSchedulerNativeGammaPrefix transitionFuel firstPause.actor
      (gammaDuplexPairs tape) 0 initialDigest [] firstPause with
  | .error failure => .error failure
  | .ok decoded =>
      if decoded.value = gamma.1 then
        .ok { decoded.response with returnedGamma := some gamma.1 }
      else
        .error .gammaMismatch

/-- The total driver starts from the actual scheduler-native first-output
scan.  An absent scan is a gamma-independent completed run. -/
def replaySchedulerNativeAtGamma
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls Result
      (gammaOutputInput nuisance.initialDigest))
    (tape : TotalGammaDuplexTape) (gamma : NonzeroQM31Exact) :
    Except SchedulerNativeGammaReplayFailure
      (SchedulerNativeGammaResponse Result) :=
  match firstScan with
  | .paused pause =>
      replaySchedulerNativeOccurrenceAtGamma transitionFuel pause tape gamma
  | .absent run =>
      .ok
        { run := run
          consumedBlocks := 0
          returnedGamma := none
          decodedBytes := none
          remainingAnswers := [] }

/-! ## Structural gamma and exact reconstruction theorems -/

theorem replay_scheduler_native_occurrence_returned_gamma_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest))
    (tape : TotalGammaDuplexTape) (gamma : NonzeroQM31Exact)
    (response : SchedulerNativeGammaResponse Result)
    (run : replaySchedulerNativeOccurrenceAtGamma transitionFuel firstPause
      tape gamma = .ok response) :
    response.returnedGamma = some gamma.1 := by
  unfold replaySchedulerNativeOccurrenceAtGamma at run
  cases prefixRun : runSchedulerNativeGammaPrefix transitionFuel
      firstPause.actor (gammaDuplexPairs tape) 0 initialDigest [] firstPause with
  | error failure =>
      simp [prefixRun] at run
  | ok decoded =>
      by_cases equal : decoded.value = gamma.1
      · simp [prefixRun, equal] at run
        cases run
        rfl
      · simp [prefixRun, equal] at run

/-- A successful occurrence is tied to the literal bytes returned by the
production decoder, not merely to an externally attached gamma label. -/
theorem replay_scheduler_native_occurrence_decoded_gamma_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest))
    (tape : TotalGammaDuplexTape) (gamma : NonzeroQM31Exact)
    (response : SchedulerNativeGammaResponse Result)
    (run : replaySchedulerNativeOccurrenceAtGamma transitionFuel firstPause
      tape gamma = .ok response) :
    ∃ encoded : Qm31Bytes,
      response.decodedBytes = some encoded ∧
      decodeTagQM31ExactLE encoded = some gamma.1 := by
  unfold replaySchedulerNativeOccurrenceAtGamma at run
  cases prefixRun : runSchedulerNativeGammaPrefix transitionFuel
      firstPause.actor (gammaDuplexPairs tape) 0 initialDigest [] firstPause with
  | error failure =>
      simp [prefixRun] at run
  | ok decoded =>
      by_cases equal : decoded.value = gamma.1
      · simp [prefixRun, equal] at run
        cases run
        refine ⟨decoded.decoded.value, ?_, ?_⟩
        exact decoded.responseBytesExact
        simpa [equal] using decoded.valueExact
      · simp [prefixRun, equal] at run

/-- Replacing one selected coordinate by its retained actual answer and then
resuming on the untouched suffix reconstructs the literal pre-scan run. -/
theorem scheduler_native_pause_actual_answer_reconstructs
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (found : scanSchedulerNativeToInput transitionFuel target cursor answers =
      .paused pause) :
    pause.resumeRunWith transitionFuel pause.targetAnswer
        pause.remainingAnswers =
      runSchedulerNativeListRun transitionFuel cursor answers := by
  rw [SchedulerNativeFreshPause.resumeRunWith_actual]
  exact scan_scheduler_native_to_input_paused_resume_exact transitionFuel
    target cursor answers pause found

/-- Exact coordinate split behind the previous reconstruction theorem. -/
theorem scheduler_native_pause_actual_answers_split
    {globalOracleCalls : Nat} {Result : Type u} {target : ShaInput}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result target)
    (found : scanSchedulerNativeToInput transitionFuel target cursor answers =
      .paused pause) :
    answers = pause.consumedAnswers ++
      pause.targetAnswer :: pause.remainingAnswers :=
  scan_scheduler_native_to_input_paused_answers_exact transitionFuel target
    cursor answers pause found

/-- The exhaustive no-output branch of the total driver is exactly the
production scheduler run and is independent of gamma and duplex data. -/
theorem replay_scheduler_native_absent_returns_actual
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) (run : SchedulerNativeRun Result)
    (absent : scanSchedulerNativeToInput transitionFuel
      (gammaOutputInput nuisance.initialDigest) cursor answers = .absent run)
    (tape : TotalGammaDuplexTape) (gamma : NonzeroQM31Exact) :
    ∃ response,
      replaySchedulerNativeAtGamma transitionFuel nuisance
          (.absent run : SchedulerNativeTargetScan globalOracleCalls Result
            (gammaOutputInput nuisance.initialDigest)) tape gamma =
            .ok response ∧
      response.run =
        runSchedulerNativeListRun transitionFuel cursor answers ∧
      response.returnedGamma = none := by
  refine ⟨
    { run := run
      consumedBlocks := 0
      returnedGamma := none
      decodedBytes := none
      remainingAnswers := [] }, rfl, ?_, rfl⟩
  exact scan_scheduler_native_to_input_absent_exact transitionFuel
    (gammaOutputInput nuisance.initialDigest) cursor answers run absent

theorem replay_scheduler_native_absent_constant
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (run : SchedulerNativeRun Result)
    (leftTape rightTape : TotalGammaDuplexTape)
    (leftGamma rightGamma : NonzeroQM31Exact) :
    replaySchedulerNativeAtGamma transitionFuel nuisance
        (.absent run : SchedulerNativeTargetScan globalOracleCalls Result
          (gammaOutputInput nuisance.initialDigest)) leftTape leftGamma =
      replaySchedulerNativeAtGamma transitionFuel nuisance
        (.absent run : SchedulerNativeTargetScan globalOracleCalls Result
          (gammaOutputInput nuisance.initialDigest)) rightTape rightGamma := by
  rfl

#print axioms replay_scheduler_native_occurrence_returned_gamma_exact
#print axioms replay_scheduler_native_occurrence_decoded_gamma_exact
#print axioms scheduler_native_pause_actual_answer_reconstructs
#print axioms scheduler_native_pause_actual_answers_split
#print axioms replay_scheduler_native_absent_returns_actual
#print axioms replay_scheduler_native_absent_constant

end

end AspisK1.V7Tag73SchedulerNativeGammaReplay
