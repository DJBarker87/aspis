import AspisFormal.K1.V7Tag73SchedulerNativeTargetPause
import AspisFormal.K1.V7Tag73VariablePrefixGammaSampler

/-!
# Scheduler-native counterfactual replay of the Tag-73 gamma sampler

This module runs the variable-prefix gamma sampler directly inside the
result-carrying scheduler.  It begins at the executable first-target scan from
`V7Tag73SchedulerNativeTargetPause`.  At each sampler coordinate it reuses an
already fixed table entry without consuming a master-tape answer, or replaces
the answer only at a genuine fresh scheduler pause.  It then scans the
ordinary scheduler over the untouched master-tape suffix until the dynamically
computed next input is reached.  Thus actor changes, arbitrary machine work,
cache hits, and atomic-fork activity between gamma queries are handled without
changing the production scheduler.

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
open AspisK1.V7Tag73OperationalCausalInjection
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
  | cachedAnswerMismatch (kind : SchedulerNativeGammaQueryKind)
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

/-- Scheduler state retained between gamma duplex coordinates.  `oracle` is
the table state at the last fresh pause (or immediately after installing its
answer).  It is used only to recognize coordinates that were already fixed;
cached recognition consumes no master-tape answer and does not mutate the
production cursor. -/
structure SchedulerNativeGammaCursor
    (globalOracleCalls : Nat) (Result : Type u) where
  cursor : SchedulerNativeCursor globalOracleCalls Result
  remainingAnswers : List Digest256
  oracle : OracleState
  tracePrefix : List UnifiedExposureRecord

/-- Consume one expected gamma coordinate.  A value already in the retained
table is immutable nuisance and must agree with the routed tape.  Otherwise
the production scheduler is scanned to a genuine fresh pause and only that
fresh answer is replaced.  The actor is whatever the actual pause reports. -/
def consumeSchedulerNativeGammaCoordinate
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (kind : SchedulerNativeGammaQueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state : SchedulerNativeGammaCursor globalOracleCalls Result) :
    Except SchedulerNativeGammaReplayFailure
      (SchedulerNativeGammaCursor globalOracleCalls Result) :=
  match lookupEntry state.oracle expectedInput with
  | some entry =>
      if entry.output = expectedAnswer then .ok state
      else .error (.cachedAnswerMismatch kind)
  | none =>
      match scanSchedulerNativeToInput transitionFuel expectedInput
          state.cursor state.remainingAnswers with
      | .absent _ => .error (.expectedQueryAbsent kind)
      | .paused pause =>
          .ok
            { cursor := pause.resumeCursorWith expectedAnswer
              remainingAnswers := pause.remainingAnswers
              oracle := freshQueryState pause.actor pause.requestState
                pause.input expectedAnswer
              tracePrefix := state.tracePrefix ++ pause.consumedTrace ++
                [machineFreshRecord pause expectedAnswer] }

theorem consume_scheduler_native_gamma_cached_is_inert
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (kind : SchedulerNativeGammaQueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state : SchedulerNativeGammaCursor globalOracleCalls Result)
    (entry : TableEntry)
    (found : lookupEntry state.oracle expectedInput = some entry)
    (answerExact : entry.output = expectedAnswer) :
    consumeSchedulerNativeGammaCoordinate transitionFuel kind expectedInput
        expectedAnswer state = .ok state := by
  simp [consumeSchedulerNativeGammaCoordinate, found, answerExact]

theorem consume_scheduler_native_gamma_fresh_uses_exact_pause_actor
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (kind : SchedulerNativeGammaQueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state : SchedulerNativeGammaCursor globalOracleCalls Result)
    (missing : lookupEntry state.oracle expectedInput = none)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result expectedInput)
    (paused : scanSchedulerNativeToInput transitionFuel expectedInput
      state.cursor state.remainingAnswers = .paused pause) :
    consumeSchedulerNativeGammaCoordinate transitionFuel kind expectedInput
        expectedAnswer state =
      .ok
        { cursor := pause.resumeCursorWith expectedAnswer
          remainingAnswers := pause.remainingAnswers
          oracle := freshQueryState pause.actor pause.requestState pause.input
            expectedAnswer
          tracePrefix := state.tracePrefix ++ pause.consumedTrace ++
            [machineFreshRecord pause expectedAnswer] } := by
  simp [consumeSchedulerNativeGammaCoordinate, missing, paused]

/-- Execute the sampler from a pause at its next output query.  The two scans
in each iteration consume arbitrary intervening scheduler coordinates from
the retained master-tape suffix.  Only the selected output and advance fresh
answers are replaced by the corresponding fixed duplex coordinates. -/
def runSchedulerNativeGammaPrefix
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) :
    (pairs : List (Digest256 × Digest256)) →
      (consumedBlocks : Nat) → (digest : Digest256) →
      (outputs : List Digest256) →
      SchedulerNativeGammaCursor globalOracleCalls Result →
      Except SchedulerNativeGammaReplayFailure
        (DecodedSchedulerNativeGammaResponse Result)
  | [], _, _, _, _ => .error .samplerTapeExhausted
  | (output, advanced) :: rest, consumedBlocks, digest, outputs, state =>
      match consumeSchedulerNativeGammaCoordinate transitionFuel .output
          (gammaOutputInput digest) output state with
      | .error failure => .error failure
      | .ok afterOutput =>
        match consumeSchedulerNativeGammaCoordinate transitionFuel .advance
            (gammaAdvanceInput digest) advanced afterOutput with
        | .error failure => .error failure
        | .ok afterAdvance =>
          let nextOutputs := outputs ++ [output]
          match _decodedRun : decodeNonzeroPrefix 3 nextOutputs with
          | some decoded =>
              match valueRun : decodeTagQM31ExactLE decoded.value with
              | none => .error .decodedValueInvalid
              | some value =>
                  let tail := runSchedulerNativeListRun transitionFuel
                    afterAdvance.cursor afterAdvance.remainingAnswers
                  .ok
                    { response :=
                        { run :=
                            { terminal := tail.terminal
                              trace := afterAdvance.tracePrefix ++ tail.trace }
                          consumedBlocks := consumedBlocks + 1
                          returnedGamma := some value
                          decodedBytes := some decoded.value
                          remainingAnswers := afterAdvance.remainingAnswers }
                      decoded := decoded
                      value := value
                      valueExact := valueRun
                      responseBytesExact := rfl }
          | none =>
              runSchedulerNativeGammaPrefix transitionFuel rest
                (consumedBlocks + 1) advanced nextOutputs afterAdvance

/-- First iteration specialized to the already-proved source pause.  The
routed output is installed directly into the pending fresh request, so the
retained realized `targetAnswer` is never read.  Later coordinates use the
cache/fresh consumer above. -/
def runSchedulerNativeGammaFromFirstPause
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest)) :
    (pairs : List (Digest256 × Digest256)) →
      Except SchedulerNativeGammaReplayFailure
        (DecodedSchedulerNativeGammaResponse Result)
  | [] => .error .samplerTapeExhausted
  | (output, advanced) :: rest =>
      let afterOutput : SchedulerNativeGammaCursor globalOracleCalls Result :=
        { cursor := firstPause.resumeCursorWith output
          remainingAnswers := firstPause.remainingAnswers
          oracle := freshQueryState firstPause.actor firstPause.requestState
            firstPause.input output
          tracePrefix := firstPause.consumedTrace ++
            [machineFreshRecord firstPause output] }
      match consumeSchedulerNativeGammaCoordinate transitionFuel .advance
          (gammaAdvanceInput initialDigest) advanced afterOutput with
      | .error failure => .error failure
      | .ok afterAdvance =>
          let outputs := [output]
          match _decodedRun : decodeNonzeroPrefix 3 outputs with
          | some decoded =>
              match valueRun : decodeTagQM31ExactLE decoded.value with
              | none => .error .decodedValueInvalid
              | some value =>
                  let tail := runSchedulerNativeListRun transitionFuel
                    afterAdvance.cursor afterAdvance.remainingAnswers
                  .ok
                    { response :=
                        { run :=
                            { terminal := tail.terminal
                              trace := afterAdvance.tracePrefix ++ tail.trace }
                          consumedBlocks := 1
                          returnedGamma := some value
                          decodedBytes := some decoded.value
                          remainingAnswers := afterAdvance.remainingAnswers }
                      decoded := decoded
                      value := value
                      valueExact := valueRun
                      responseBytesExact := rfl }
          | none =>
              runSchedulerNativeGammaPrefix transitionFuel rest 1 advanced
                outputs afterAdvance

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
  match runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
      (gammaDuplexPairs tape) with
  | .error failure => .error failure
  | .ok decoded =>
      if decoded.value = gamma.1 then
        .ok { decoded.response with returnedGamma := some gamma.1 }
      else
        .error .gammaMismatch

/-- The counterfactual family does not inspect the realized answer retained
by the source scan.  Replacing only that bookkeeping field leaves every
branch definitionally unchanged; the routed tape supplies the first output. -/
@[simp] theorem replay_scheduler_native_occurrence_independent_of_target_answer
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest))
    (replacement : Digest256)
    (tape : TotalGammaDuplexTape) (gamma : NonzeroQM31Exact) :
    replaySchedulerNativeOccurrenceAtGamma transitionFuel
        { firstPause with targetAnswer := replacement } tape gamma =
      replaySchedulerNativeOccurrenceAtGamma transitionFuel firstPause tape
        gamma := by
  rfl

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
  dsimp only at run
  cases prefixRun : runSchedulerNativeGammaFromFirstPause transitionFuel
      firstPause (gammaDuplexPairs tape) with
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
  dsimp only at run
  cases prefixRun : runSchedulerNativeGammaFromFirstPause transitionFuel
      firstPause (gammaDuplexPairs tape) with
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
#print axioms
  replay_scheduler_native_occurrence_independent_of_target_answer
#print axioms consume_scheduler_native_gamma_cached_is_inert
#print axioms
  consume_scheduler_native_gamma_fresh_uses_exact_pause_actor
#print axioms scheduler_native_pause_actual_answer_reconstructs
#print axioms scheduler_native_pause_actual_answers_split
#print axioms replay_scheduler_native_absent_returns_actual
#print axioms replay_scheduler_native_absent_constant

end

end AspisK1.V7Tag73SchedulerNativeGammaReplay
