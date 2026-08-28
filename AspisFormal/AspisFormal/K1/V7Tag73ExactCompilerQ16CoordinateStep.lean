import AspisFormal.K1.V7Tag73ExactCompilerActualGammaReplayClosure
import AspisFormal.K1.V7Tag73SchedulerNativeQ16Replay

/-!
# Exact-compiler q16 coordinate step

The gamma and q16 replay engines deliberately retain the same executable
scheduler cursor.  This file makes that representation equality explicit and
transports the source-anchored cache-or-future coordinate theorem to q16.

In particular, a q16 coordinate first created by an adversary is handled as an
immutable cache hit.  It is not relabelled as a fresh verifier query and no
freshness or small-bad-event premise is introduced.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerQ16CoordinateStep

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
open AspisK1.V7Tag73ExactCompilerActualGammaReplayClosure

noncomputable section

universe u

/-- The q16 cursor viewed through the already-proved source-anchored gamma
cursor invariant.  No state is erased or synthesized. -/
def q16CursorToGamma
    {globalOracleCalls : Nat} {Result : Type u}
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    SchedulerNativeGammaCursor globalOracleCalls Result :=
  { cursor := state.cursor
    remainingAnswers := state.remainingAnswers
    oracle := state.oracle
    tracePrefix := state.tracePrefix }

/-- The inverse representation map. -/
def gammaCursorToQ16
    {globalOracleCalls : Nat} {Result : Type u}
    (state : SchedulerNativeGammaCursor globalOracleCalls Result) :
    SchedulerNativeQ16Cursor globalOracleCalls Result :=
  { cursor := state.cursor
    remainingAnswers := state.remainingAnswers
    oracle := state.oracle
    tracePrefix := state.tracePrefix }

@[simp] theorem q16_cursor_to_gamma_to_q16
    {globalOracleCalls : Nat} {Result : Type u}
    (state : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    gammaCursorToQ16 (q16CursorToGamma state) = state := by
  cases state
  rfl

@[simp] theorem gamma_cursor_to_q16_to_gamma
    {globalOracleCalls : Nat} {Result : Type u}
    (state : SchedulerNativeGammaCursor globalOracleCalls Result) :
    q16CursorToGamma (gammaCursorToQ16 state) = state := by
  cases state
  rfl

def q16KindToGamma :
    SchedulerNativeQ16QueryKind → SchedulerNativeGammaQueryKind
  | .output => .output
  | .advance => .advance

/-- A successful q16 coordinate transition is exactly the corresponding
gamma-cursor transition after the representation map.  Failure constructors
are intentionally not identified: only successful executable state flow is
transported. -/
theorem consume_q16_coordinate_ok_iff_gamma
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (kind : SchedulerNativeQ16QueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state next : SchedulerNativeQ16Cursor globalOracleCalls Result) :
    consumeSchedulerNativeQ16Coordinate transitionFuel kind expectedInput
        expectedAnswer state = .ok next ↔
      consumeSchedulerNativeGammaCoordinate transitionFuel
        (q16KindToGamma kind) expectedInput expectedAnswer
        (q16CursorToGamma state) = .ok (q16CursorToGamma next) := by
  cases state with
  | mk cursor remainingAnswers oracle tracePrefix =>
      cases next with
      | mk nextCursor nextAnswers nextOracle nextTrace =>
          unfold consumeSchedulerNativeQ16Coordinate
            consumeSchedulerNativeGammaCoordinate q16CursorToGamma
          cases found : lookupEntry oracle expectedInput with
          | some entry =>
              by_cases answerExact : entry.output = expectedAnswer <;>
                simp [answerExact]
          | none =>
              cases paused : scanSchedulerNativeToInput transitionFuel
                  expectedInput cursor remainingAnswers with
              | absent tail => simp
              | paused pause =>
                  simp [q16MachineFreshRecord, machineFreshRecord]

/-- The q16 form of the source-anchored alignment invariant. -/
def ExactCompilerRootQ16CursorAligned
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
    (state : SchedulerNativeQ16Cursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)) : Type :=
  ExactCompilerRootGammaCursorAligned input (q16CursorToGamma state)

/-- Minimal one-coordinate q16 interface used by branch/forest induction. -/
def ExactCompilerQ16CoordinateStep
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Prop :=
  ∀ (kind : SchedulerNativeQ16QueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state : SchedulerNativeQ16Cursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result)),
    ExactCompilerRootQ16CursorAligned input state →
    tableLookup (exactOperationalTable input) expectedInput =
        some expectedAnswer →
      ∃ nextState,
        consumeSchedulerNativeQ16Coordinate transitionFuel kind expectedInput
            expectedAnswer state = .ok nextState ∧
        Nonempty (ExactCompilerRootQ16CursorAligned input nextState)

/-- Actual q16 coordinates inherit the proved cache-or-future source
alignment.  This is the adversary-first-safe coordinate endpoint. -/
theorem exact_compiler_actual_q16_coordinate_step
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
      fixedInstance sample) :
    ExactCompilerQ16CoordinateStep input := by
  intro kind expectedInput expectedAnswer state aligned found
  obtain ⟨gammaNext, gammaConsumed, gammaAligned⟩ :=
    exact_compiler_actual_gamma_coordinate_step transitionRoom input
      (q16KindToGamma kind) expectedInput expectedAnswer
      (q16CursorToGamma state) aligned found
  let next := gammaCursorToQ16 gammaNext
  refine ⟨next, ?_, ?_⟩
  · apply (consume_q16_coordinate_ok_iff_gamma transitionFuel kind
      expectedInput expectedAnswer state next).2
    simpa [next] using gammaConsumed
  · rcases gammaAligned with ⟨gammaAligned⟩
    exact ⟨by simpa [ExactCompilerRootQ16CursorAligned, next] using
      gammaAligned⟩

#print axioms consume_q16_coordinate_ok_iff_gamma
#print axioms exact_compiler_actual_q16_coordinate_step

end

end AspisK1.V7Tag73ExactCompilerQ16CoordinateStep
