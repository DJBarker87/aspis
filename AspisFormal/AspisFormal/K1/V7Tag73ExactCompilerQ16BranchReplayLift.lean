import AspisFormal.K1.V7Tag73ExactCompilerQ16BranchCoordinates
import AspisFormal.K1.V7Tag73ExactCompilerSchedulerPauseBinding
import AspisFormal.K1.V7Tag73SchedulerNativeQ16ForestReplay

/-!
# Lift exact q16 coordinates through an executable branch

The local source-anchored coordinate theorem is folded across every duplex
pair.  Both cached and fresh coordinates preserve the same chronological root
alignment, so the result applies without classifying who first queried a q16
coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerQ16BranchReplayLift

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73SchedulerNativeQ16ForestReplay
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerQ16CoordinateStep
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut

noncomputable section

/-- Fold the one-coordinate theorem across a complete output/advance chain. -/
theorem run_scheduler_native_q16_branch_tail_actual_chain
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
    (coordinateStep : ExactCompilerQ16CoordinateStep input) :
    ∀ {digest : Digest256} {outputs advances : List Digest256},
      GammaTableCoordinateChain (exactOperationalTable input) digest outputs
          advances →
      ∀ (state : SchedulerNativeQ16Cursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)),
        ExactCompilerRootQ16CursorAligned input state →
        ∃ final,
          runSchedulerNativeQ16BranchTail transitionFuel
              (outputs.zip advances) digest state = .ok final ∧
          Nonempty (ExactCompilerRootQ16CursorAligned input final) := by
  intro digest outputs advances chain
  induction chain with
  | done digest =>
      intro state aligned
      exact ⟨state, rfl, ⟨aligned⟩⟩
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail ih =>
      intro state aligned
      obtain ⟨afterOutput, outputRun, ⟨outputAligned⟩⟩ :=
        coordinateStep .output (q16OutputInput digest) output state aligned
          (by simpa [q16OutputInput, gammaOutputInput] using outputLookup)
      obtain ⟨afterAdvance, advanceRun, ⟨advanceAligned⟩⟩ :=
        coordinateStep .advance (q16AdvanceInput digest) advanced afterOutput
          outputAligned
          (by simpa [q16AdvanceInput, gammaAdvanceInput] using advanceLookup)
      obtain ⟨final, tailRun, finalAligned⟩ :=
        ih afterAdvance advanceAligned
      refine ⟨final, ?_, finalAligned⟩
      simp only [List.zip_cons_cons, runSchedulerNativeQ16BranchTail]
      rw [outputRun]
      simp only
      rw [advanceRun]
      exact tailRun

/-- A nonempty exact coordinate chain executes the branch-from-cursor entry
point and preserves source alignment. -/
theorem run_scheduler_native_q16_branch_from_cursor_actual_chain
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
    (coordinateStep : ExactCompilerQ16CoordinateStep input)
    (branch : SchedulerNativeQ16Branch) (forest : TotalQ16DuplexForest)
    (outputs advances : List Digest256)
    (chain : GammaTableCoordinateChain (exactOperationalTable input)
      branch.initialDigest outputs advances)
    (outputsPositive : outputs ≠ [])
    (pairsExact : q16BranchDuplexPairs branch forest = outputs.zip advances)
    (state : SchedulerNativeQ16Cursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (aligned : ExactCompilerRootQ16CursorAligned input state) :
    ∃ final,
      runSchedulerNativeQ16BranchFromCursor transitionFuel branch forest state =
        .ok final ∧
      Nonempty (ExactCompilerRootQ16CursorAligned input final) := by
  cases chain with
  | done digest =>
      exact (outputsPositive rfl).elim
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail =>
      obtain ⟨afterOutput, outputRun, ⟨outputAligned⟩⟩ :=
        coordinateStep .output (q16OutputInput branch.initialDigest) output
          state aligned
          (by simpa [q16OutputInput, gammaOutputInput] using outputLookup)
      obtain ⟨afterAdvance, advanceRun, ⟨advanceAligned⟩⟩ :=
        coordinateStep .advance (q16AdvanceInput branch.initialDigest) advanced
          afterOutput outputAligned
          (by simpa [q16AdvanceInput, gammaAdvanceInput] using advanceLookup)
      obtain ⟨final, tailRun, finalAligned⟩ :=
        run_scheduler_native_q16_branch_tail_actual_chain input coordinateStep
          tail afterAdvance advanceAligned
      refine ⟨final, ?_, finalAligned⟩
      unfold runSchedulerNativeQ16BranchFromCursor
      rw [pairsExact]
      simp only [List.zip_cons_cons]
      rw [outputRun]
      simp only
      rw [advanceRun]
      exact tailRun

/-- The first-pause entry point executes one literal q16 branch on the
production coordinates.  The initial output is installed at the exact
chronological pause; every later coordinate is consumed through the ordinary
cache-aware source alignment.  In particular, the theorem makes no claim
that the pause actor is a verifier. -/
theorem run_scheduler_native_q16_branch_from_first_pause_actual_chain
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
    (coordinateStep : ExactCompilerQ16CoordinateStep input)
    (branch : SchedulerNativeQ16Branch) (forest : TotalQ16DuplexForest)
    (outputs advances : List Digest256)
    (chain : GammaTableCoordinateChain (exactOperationalTable input)
      branch.initialDigest outputs advances)
    (outputsPositive : outputs ≠ [])
    (pairsExact : q16BranchDuplexPairs branch forest = outputs.zip advances)
    (firstPause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (q16OutputInput branch.initialDigest))
    (paused : exactCompilerFullTargetScan input
      (q16OutputInput branch.initialDigest) = .paused firstPause) :
    ∃ final,
      runSchedulerNativeQ16BranchFromFirstPause transitionFuel branch
          firstPause forest = .ok final ∧
      Nonempty (ExactCompilerRootQ16CursorAligned input final) := by
  cases chain with
  | done digest =>
      exact (outputsPositive rfl).elim
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail =>
      let initial := exactCompilerInitialQ16Cursor input
      let directAfterOutput : SchedulerNativeQ16Cursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result) :=
        { cursor := firstPause.resumeCursorWith output
          remainingAnswers := firstPause.remainingAnswers
          oracle := freshQueryState firstPause.actor firstPause.requestState
            firstPause.input output
          tracePrefix := initial.tracePrefix ++ firstPause.consumedTrace ++
            [q16MachineFreshRecord firstPause output] }
      have scanned : scanSchedulerNativeToInput transitionFuel
          (q16OutputInput branch.initialDigest) initial.cursor
          initial.remainingAnswers = .paused firstPause := by
        exact paused
      have missing : lookupEntry initial.oracle
          (q16OutputInput branch.initialDigest) = none := by
        rfl
      have directOutputRun :
          consumeSchedulerNativeQ16Coordinate transitionFuel .output
              (q16OutputInput branch.initialDigest) output initial =
            .ok directAfterOutput := by
        simpa [directAfterOutput, initial, exactCompilerInitialQ16Cursor,
          q16MachineFreshRecord] using
          consume_scheduler_native_q16_fresh_uses_exact_pause_actor
            transitionFuel .output (q16OutputInput branch.initialDigest) output
            initial missing firstPause scanned
      obtain ⟨afterOutput, outputRun, ⟨afterOutputAligned⟩⟩ :=
        coordinateStep .output (q16OutputInput branch.initialDigest) output
          initial (exactCompilerInitialQ16CursorAlignment input)
          (by simpa [q16OutputInput, gammaOutputInput] using outputLookup)
      have afterOutputExact : afterOutput = directAfterOutput := by
        rw [directOutputRun] at outputRun
        exact Except.ok.inj outputRun.symm
      subst afterOutput
      have directAfterOutputExact : directAfterOutput =
          { cursor := firstPause.resumeCursorWith output
            remainingAnswers := firstPause.remainingAnswers
            oracle := freshQueryState firstPause.actor firstPause.requestState
              firstPause.input output
            tracePrefix := firstPause.consumedTrace ++
              [q16MachineFreshRecord firstPause output] } := by
        simp [directAfterOutput, initial, exactCompilerInitialQ16Cursor,
          gammaCursorToQ16, exactCompilerInitialGammaCursor]
      obtain ⟨afterAdvance, advanceRun, ⟨afterAdvanceAligned⟩⟩ :=
        coordinateStep .advance (q16AdvanceInput branch.initialDigest) advanced
          directAfterOutput afterOutputAligned
          (by simpa [q16AdvanceInput, gammaAdvanceInput] using advanceLookup)
      have advanceRunDirect :
          consumeSchedulerNativeQ16Coordinate transitionFuel .advance
              (q16AdvanceInput branch.initialDigest) advanced
              { cursor := firstPause.resumeCursorWith output
                remainingAnswers := firstPause.remainingAnswers
                oracle := freshQueryState firstPause.actor
                  firstPause.requestState firstPause.input output
                tracePrefix := firstPause.consumedTrace ++
                  [q16MachineFreshRecord firstPause output] } =
            .ok afterAdvance := by
        rw [← directAfterOutputExact]
        exact advanceRun
      obtain ⟨final, tailRun, finalAligned⟩ :=
        run_scheduler_native_q16_branch_tail_actual_chain input coordinateStep
          tail afterAdvance afterAdvanceAligned
      refine ⟨final, ?_, finalAligned⟩
      unfold runSchedulerNativeQ16BranchFromFirstPause
      rw [pairsExact]
      simp only [List.zip_cons_cons]
      rw [advanceRunDirect]
      exact tailRun

#print axioms run_scheduler_native_q16_branch_tail_actual_chain
#print axioms run_scheduler_native_q16_branch_from_cursor_actual_chain
#print axioms run_scheduler_native_q16_branch_from_first_pause_actual_chain

end

end AspisK1.V7Tag73ExactCompilerQ16BranchReplayLift
